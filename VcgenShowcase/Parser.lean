import Std.Internal.Do
import Std.Tactic.Do
import VcgenShowcase.StackMachine

/-!
# A verified recursive-descent parser and the parse-compile-execute pipeline

Grammar, left-associative with `*` binding tighter than `+`:

    expr   ::= term ('+' term)*
    term   ::= factor ('*' factor)*
    factor ::= nat | '(' expr ')'

`ParserM` is `ExceptT String (StateM (List Char))`; the five mutual parsers recurse
on explicit fuel. The printers invert one grammar level each, parenthesizing exactly
where the grammar demands it. `NonnegLits` is the printable fragment (numeric
literals are nonnegative).

Main results:

* `roundtrip`: for `NonnegLits e`, running `parseExpr` on `printExpr e ++ rest`
  returns `e` and leaves exactly `rest`, stated as a `Triple` per grammar level and
  proved by a single induction over `e`. Each case composes eight `vcgen`-proved
  core lemmas (`core_E`, `core_T_seq`, ...), each a one-line
  `rw; vcgen; all_goals grind`.
* `parse_print_run` and `compile_correct_run`: pure equations extracted from the
  triples via `Triple.le_wp`, the transformer `wp_apply_eq` simp set, and
  `Id.of_wp_run_eq`; the error branch is refuted by reducing `EPost.Cons.pushExcept`
  at the `.error` constructor and `bot_le`.
* `evalString_print`: the pipeline capstone. `evalString` parses a string, compiles
  the expression with `Expr.compile`, runs the stack machine, and returns the top of
  stack; on a printed expression it yields `.ok e.denote`. The proof is two rewrites:
  `parse_print_run` and `compile_correct_run`.

Load-bearing techniques, each of which costs an afternoon when missed:

1. Canonical specs. Every `@[spec]` precondition is `fun s => s = X` with `X` built
   from `takeWhile`/`dropWhile` (`parseNat` returns
   `valDigits 0 (s0.takeWhile Char.isDigit)` and leaves `s0.dropWhile Char.isDigit`),
   so the spec applies to any input shape by first-order unification; a precondition
   `fun s => s = ds ++ rest` leaves unsolvable `?vc` metavariables at every call site.
2. Accumulator generality. Specs for the tail parsers and `parseNatAux` quantify
   over the accumulator, because call sites pass do-bound variables.
3. Character facts as conditional rules: `c = '(' → c.isDigit = false` with
   `grind_pattern ... => c.isDigit`. Ground facts about character literals evaporate
   during normalization before grind can chain them.
4. The composition cores take their callee triples as binder hypotheses. A
   tactic-level `have` of a `Triple` poisons the next `vcgen` call in the same proof
   ("could not determine the program type of the goal"), and neither `revert`/`intro`
   nor `obtain` cleanses the goal; hypotheses bound by the theorem binder are picked
   up as specs correctly.
5. Associativity bridges. A core's spec matches `printTerm a ++ ('+' :: mid)`, but
   the induction case sees `(printTerm a ++ '+' :: printTerm b) ++ rest`; a
   `rw [show ... from by simp [List.append_assoc]]` re-associates before the core
   unifies.
6. Definitions that recurse over `List Char` (`natDigits`, `valDigits`) get their
   equations as tactic-proved `@[grind =]` lemmas over a `foldl` body; marking the
   recursive definition itself `@[grind]` diverges in `whnf`.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false
set_option linter.unusedVariables false

abbrev ParserM := ExceptT String (StateM (List Char))

def expect (c : Char) : ParserM Unit := do
  match ← get with
  | c' :: cs => if c = c' then set cs else throw "unexpected character"
  | [] => throw "unexpected end of input"

@[spec] theorem expect_spec (c : Char) (s0 : List Char) (h : s0.head? = some c) :
    ⦃ fun s => s = s0 ⦄
    expect c
    ⦃ fun _ s => s = s0.tail ⦄ := by
  vcgen [expect]
  all_goals grind

/-- The numeric value of a digit character. -/
def digitVal (d : Char) : Nat := d.toNat - 48

/-- Digits accumulated left to right at base ten. -/
def valDigits (acc : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun a d => 10 * a + digitVal d) acc

@[grind =] theorem valDigits_nil (acc : Nat) : valDigits acc [] = acc := rfl
@[grind =] theorem valDigits_cons (acc : Nat) (d : Char) (ds : List Char) :
    valDigits acc (d :: ds) = valDigits (10 * acc + digitVal d) ds := by
  unfold valDigits
  rw [List.foldl_cons]

def parseNatAux : Nat → Nat → ParserM Nat
  | 0, _ => throw "out of fuel"
  | fuel + 1, acc => do
    match ← get with
    | d :: cs =>
      if d.isDigit then
        set cs
        parseNatAux fuel (10 * acc + digitVal d)
      else
        pure acc
    | [] => pure acc

def parseNat (fuel : Nat) : ParserM Nat := do
  match ← get with
  | d :: cs =>
    if d.isDigit then
      set cs
      parseNatAux fuel (digitVal d)
    else
      throw "expected digit"
  | [] => throw "expected digit"

/-- `parseNatAux` consumes exactly the leading digit run and accumulates its value. -/
@[spec] theorem parseNatAux_spec (s0 : List Char) (acc fuel : Nat)
    (hfuel : (s0.takeWhile Char.isDigit).length < fuel) :
    ⦃ fun s => s = s0 ⦄
    parseNatAux fuel acc
    ⦃ fun r s => r = valDigits acc (s0.takeWhile Char.isDigit) ∧
        s = s0.dropWhile Char.isDigit ⦄ := by
  induction fuel generalizing s0 acc with
  | zero => omega
  | succ fuel ih =>
    simp only [parseNatAux]
    vcgen (errorOnMissingSpec := false)
    all_goals grind [List.takeWhile_cons, List.dropWhile_cons, List.takeWhile_nil, List.dropWhile_nil]

/-- `parseNat` on input starting with a digit parses the leading digit run. -/
@[spec] theorem parseNat_spec (s0 : List Char) (fuel : Nat)
    (hd : ∀ c, s0.head? = some c → c.isDigit) (hne : s0 ≠ [])
    (hfuel : (s0.takeWhile Char.isDigit).length < fuel) :
    ⦃ fun s => s = s0 ⦄
    parseNat fuel
    ⦃ fun r s => r = valDigits 0 (s0.takeWhile Char.isDigit) ∧
        s = s0.dropWhile Char.isDigit ⦄ := by
  vcgen [parseNat]
  all_goals grind [List.takeWhile_cons, List.dropWhile_cons]

/-! ## Printing numbers -/

def natDigits (n : Nat) : List Char :=
  if h : n < 10 then [Char.ofNat (48 + n)]
  else natDigits (n / 10) ++ [Char.ofNat (48 + n % 10)]
decreasing_by omega

theorem isDigit_ofNat {m : Nat} (hm : m < 10) : (Char.ofNat (48 + m)).isDigit := by
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 := by
    omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem digitVal_ofNat {m : Nat} (hm : m < 10) : digitVal (Char.ofNat (48 + m)) = m := by
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 := by
    omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem natDigits_all_digit (n : Nat) : ∀ c ∈ natDigits n, c.isDigit := by
  induction n using natDigits.induct with
  | case1 n h =>
    unfold natDigits
    simp only [dif_pos h]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact isDigit_ofNat h
  | case2 n h ih =>
    unfold natDigits
    simp only [dif_neg h]
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ih c hc
    · simp only [List.mem_singleton] at hc
      subst hc
      exact isDigit_ofNat (by omega)

theorem valDigits_append (acc : Nat) (l₁ l₂ : List Char) :
    valDigits acc (l₁ ++ l₂) = valDigits (valDigits acc l₁) l₂ := by
  unfold valDigits
  rw [List.foldl_append]

theorem valDigits_natDigits (n : Nat) : valDigits 0 (natDigits n) = n := by
  induction n using natDigits.induct with
  | case1 n h =>
    unfold natDigits
    simp only [dif_pos h]
    rw [valDigits_cons, valDigits_nil, digitVal_ofNat h]
    omega
  | case2 n h ih =>
    unfold natDigits
    simp only [dif_neg h]
    rw [valDigits_append, ih, valDigits_cons, valDigits_nil,
      digitVal_ofNat (by omega)]
    omega

/-- Maximal munch over an all-digit run followed by a non-digit boundary. -/
theorem takeWhile_digits_append (l rest : List Char)
    (hl : ∀ c ∈ l, c.isDigit) (hrest : ∀ c, rest.head? = some c → ¬ c.isDigit) :
    (l ++ rest).takeWhile Char.isDigit = l ∧
    (l ++ rest).dropWhile Char.isDigit = rest := by
  induction l with
  | nil =>
    cases rest with
    | nil => simp
    | cons c cs =>
      have := hrest c rfl
      simp [this]
  | cons d l ih =>
    have hd := hl d List.mem_cons_self
    have := ih (fun c hc => hl c (List.mem_cons_of_mem d hc))
    simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons, hd]
    grind

/-! ## The grammar printers -/

mutual
def printExpr : Expr → List Char
  | .num n => natDigits n.toNat
  | .add a b => printTerm a ++ '+' :: printTerm b
  | .mul a b => printFactor a ++ '*' :: printFactor b
def printTerm : Expr → List Char
  | .num n => natDigits n.toNat
  | .add a b => '(' :: ((printTerm a ++ '+' :: printTerm b) ++ [')'])
  | .mul a b => printFactor a ++ '*' :: printFactor b
def printFactor : Expr → List Char
  | .num n => natDigits n.toNat
  | .add a b => '(' :: ((printTerm a ++ '+' :: printTerm b) ++ [')'])
  | .mul a b => '(' :: ((printFactor a ++ '*' :: printFactor b) ++ [')'])
end

/-! ## The parsers -/

mutual
def parseExpr (fuel : Nat) : ParserM Expr := do
  let t ← parseTerm fuel
  parseExprTail fuel t
termination_by (fuel, 3)

def parseExprTail (fuel : Nat) (acc : Expr) : ParserM Expr := do
  match ← get with
  | '+' :: cs =>
    match fuel with
    | 0 => throw "out of fuel"
    | fuel + 1 => do
      set cs
      let t ← parseTerm fuel
      parseExprTail fuel (.add acc t)
  | _ => pure acc
termination_by (fuel, 1)

def parseTerm (fuel : Nat) : ParserM Expr := do
  let f ← parseFactor fuel
  parseTermTail fuel f
termination_by (fuel, 2)

def parseTermTail (fuel : Nat) (acc : Expr) : ParserM Expr := do
  match ← get with
  | '*' :: cs =>
    match fuel with
    | 0 => throw "out of fuel"
    | fuel + 1 => do
      set cs
      let f ← parseFactor fuel
      parseTermTail fuel (.mul acc f)
  | _ => pure acc
termination_by (fuel, 1)

def parseFactor (fuel : Nat) : ParserM Expr := do
  match ← get with
  | '(' :: cs =>
    match fuel with
    | 0 => throw "out of fuel"
    | fuel + 1 => do
      set cs
      let e ← parseExpr fuel
      expect ')'
      pure e
  | _ => do
    let n ← parseNat fuel
    pure (.num n)
termination_by (fuel, 0)
end

/-! ## Round trip -/

theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  unfold natDigits
  split <;> simp

theorem natDigits_head_digit (n : Nat) : ∀ c, (natDigits n).head? = some c → c.isDigit := by
  intro c hc
  have hmem : c ∈ natDigits n := by
    cases h : natDigits n with
    | nil => simp [h] at hc
    | cons x xs => simp [h] at hc; simp [hc]
  exact natDigits_all_digit n c hmem

/-- Nonnegative numeric literals, the printable fragment. -/
def NonnegLits : Expr → Prop
  | .num n => 0 ≤ n
  | .add a b => NonnegLits a ∧ NonnegLits b
  | .mul a b => NonnegLits a ∧ NonnegLits b

@[grind =] theorem NonnegLits_num (n : Int) : NonnegLits (.num n) = (0 ≤ n) := rfl
@[grind =] theorem NonnegLits_add (a b : Expr) :
    NonnegLits (.add a b) = (NonnegLits a ∧ NonnegLits b) := rfl
@[grind =] theorem NonnegLits_mul (a b : Expr) :
    NonnegLits (.mul a b) = (NonnegLits a ∧ NonnegLits b) := rfl

/-- Round-trip statement at expression level. -/
abbrev QE (e : Expr) : Prop := NonnegLits e → ∀ rest fuel,
  rest.head? ≠ some '+' → rest.head? ≠ some '*' →
  (∀ c, rest.head? = some c → ¬ c.isDigit) →
  (printExpr e ++ rest).length < fuel →
  ⦃ fun s => s = printExpr e ++ rest ⦄ parseExpr fuel ⦃ fun r s => r = e ∧ s = rest ⦄

/-- Round-trip statement at term level. -/
abbrev QT (e : Expr) : Prop := NonnegLits e → ∀ rest fuel,
  rest.head? ≠ some '*' →
  (∀ c, rest.head? = some c → ¬ c.isDigit) →
  (printTerm e ++ rest).length < fuel →
  ⦃ fun s => s = printTerm e ++ rest ⦄ parseTerm fuel ⦃ fun r s => r = e ∧ s = rest ⦄

/-- Round-trip statement at factor level. -/
abbrev QF (e : Expr) : Prop := NonnegLits e → ∀ rest fuel,
  (∀ c, rest.head? = some c → ¬ c.isDigit) →
  (printFactor e ++ rest).length < fuel →
  ⦃ fun s => s = printFactor e ++ rest ⦄ parseFactor fuel ⦃ fun r s => r = e ∧ s = rest ⦄

theorem exprTail_stop (rest : List Char) (fuel : Nat) (acc : Expr)
    (h : rest.head? ≠ some '+') :
    ⦃ fun s => s = rest ⦄ parseExprTail fuel acc ⦃ fun r s => r = acc ∧ s = rest ⦄ := by
  rw [parseExprTail]
  vcgen (errorOnMissingSpec := false)
  all_goals grind

theorem termTail_stop (rest : List Char) (fuel : Nat) (acc : Expr)
    (h : rest.head? ≠ some '*') :
    ⦃ fun s => s = rest ⦄ parseTermTail fuel acc ⦃ fun r s => r = acc ∧ s = rest ⦄ := by
  rw [parseTermTail]
  vcgen (errorOnMissingSpec := false)
  all_goals grind

theorem plus_not_digit (c : Char) : c = '+' → c.isDigit = false := by rintro rfl; decide
theorem star_not_digit (c : Char) : c = '*' → c.isDigit = false := by rintro rfl; decide
theorem lparen_not_digit (c : Char) : c = '(' → c.isDigit = false := by rintro rfl; decide
theorem rparen_not_digit (c : Char) : c = ')' → c.isDigit = false := by rintro rfl; decide

grind_pattern plus_not_digit => c.isDigit
grind_pattern star_not_digit => c.isDigit
grind_pattern lparen_not_digit => c.isDigit
grind_pattern rparen_not_digit => c.isDigit

/-! ### Composition cores

Each core takes its callee specs as binders: a tactic-`have` of a `Triple` poisons
the next `vcgen` (it fails to determine the program type of an unchanged goal), while
binder hypotheses are picked up as specs correctly. -/

private theorem core_T (t : Expr) (s0 rest : List Char) (fuel : Nat)
    (hFi : ⦃ fun s => s = s0 ⦄ parseFactor fuel ⦃ fun r s => r = t ∧ s = rest ⦄)
    (hstop : ∀ acc : Expr,
      ⦃ fun s => s = rest ⦄ parseTermTail fuel acc ⦃ fun r s => r = acc ∧ s = rest ⦄) :
    ⦃ fun s => s = s0 ⦄ parseTerm fuel ⦃ fun r s => r = t ∧ s = rest ⦄ := by
  rw [parseTerm]
  vcgen (errorOnMissingSpec := false)
  all_goals grind

private theorem core_E (t : Expr) (s0 rest : List Char) (fuel : Nat)
    (hTi : ⦃ fun s => s = s0 ⦄ parseTerm fuel ⦃ fun r s => r = t ∧ s = rest ⦄)
    (hstop : ∀ acc : Expr,
      ⦃ fun s => s = rest ⦄ parseExprTail fuel acc ⦃ fun r s => r = acc ∧ s = rest ⦄) :
    ⦃ fun s => s = s0 ⦄ parseExpr fuel ⦃ fun r s => r = t ∧ s = rest ⦄ := by
  rw [parseExpr]
  vcgen (errorOnMissingSpec := false)
  all_goals grind

private theorem core_ET_step (b : Expr) (mid rest : List Char) (fuel : Nat)
    (hTb : ⦃ fun s => s = mid ⦄ parseTerm fuel ⦃ fun r s => r = b ∧ s = rest ⦄)
    (hstop : ∀ acc : Expr,
      ⦃ fun s => s = rest ⦄ parseExprTail fuel acc ⦃ fun r s => r = acc ∧ s = rest ⦄) :
    ∀ acc : Expr, ⦃ fun s => s = '+' :: mid ⦄ parseExprTail (fuel + 1) acc
      ⦃ fun r s => r = Expr.add acc b ∧ s = rest ⦄ := by
  intro acc
  rw [parseExprTail]
  vcgen (errorOnMissingSpec := false)
  all_goals grind

private theorem core_TT_step (b : Expr) (mid rest : List Char) (fuel : Nat)
    (hFb : ⦃ fun s => s = mid ⦄ parseFactor fuel ⦃ fun r s => r = b ∧ s = rest ⦄)
    (hstop : ∀ acc : Expr,
      ⦃ fun s => s = rest ⦄ parseTermTail fuel acc ⦃ fun r s => r = acc ∧ s = rest ⦄) :
    ∀ acc : Expr, ⦃ fun s => s = '*' :: mid ⦄ parseTermTail (fuel + 1) acc
      ⦃ fun r s => r = Expr.mul acc b ∧ s = rest ⦄ := by
  intro acc
  rw [parseTermTail]
  vcgen (errorOnMissingSpec := false)
  all_goals grind

private theorem core_T_seq (a b : Expr) (s0 mid rest : List Char) (fuel : Nat)
    (hFa : ⦃ fun s => s = s0 ⦄ parseFactor (fuel + 1) ⦃ fun r s => r = a ∧ s = '*' :: mid ⦄)
    (hstep : ∀ acc : Expr, ⦃ fun s => s = '*' :: mid ⦄ parseTermTail (fuel + 1) acc
      ⦃ fun r s => r = Expr.mul acc b ∧ s = rest ⦄) :
    ⦃ fun s => s = s0 ⦄ parseTerm (fuel + 1) ⦃ fun r s => r = Expr.mul a b ∧ s = rest ⦄ := by
  rw [parseTerm]
  vcgen (errorOnMissingSpec := false)
  all_goals grind

private theorem core_E_seq (a b : Expr) (s0 mid rest : List Char) (fuel : Nat)
    (hTa : ⦃ fun s => s = s0 ⦄ parseTerm (fuel + 1) ⦃ fun r s => r = a ∧ s = '+' :: mid ⦄)
    (hstep : ∀ acc : Expr, ⦃ fun s => s = '+' :: mid ⦄ parseExprTail (fuel + 1) acc
      ⦃ fun r s => r = Expr.add acc b ∧ s = rest ⦄) :
    ⦃ fun s => s = s0 ⦄ parseExpr (fuel + 1) ⦃ fun r s => r = Expr.add a b ∧ s = rest ⦄ := by
  rw [parseExpr]
  vcgen (errorOnMissingSpec := false)
  all_goals grind

private theorem core_F_group (e : Expr) (inner rest : List Char) (fuel : Nat)
    (hEi : ⦃ fun s => s = inner ⦄ parseExpr fuel ⦃ fun r s => r = e ∧ s = ')' :: rest ⦄) :
    ⦃ fun s => s = '(' :: inner ⦄ parseFactor (fuel + 1) ⦃ fun r s => r = e ∧ s = rest ⦄ := by
  rw [parseFactor]
  vcgen (errorOnMissingSpec := false)
  all_goals grind

private theorem core_F_num (n : Int) (hnn : 0 ≤ n) (rest : List Char) (fuel : Nat)
    (hdig : ∀ c, rest.head? = some c → ¬ c.isDigit)
    (hfuel : (natDigits n.toNat ++ rest).length < fuel) :
    ⦃ fun s => s = natDigits n.toNat ++ rest ⦄ parseFactor fuel
    ⦃ fun r s => r = Expr.num n ∧ s = rest ⦄ := by
  obtain ⟨htake, hdrop⟩ := takeWhile_digits_append (natDigits n.toNat) rest
    (natDigits_all_digit _) hdig
  obtain ⟨d, ds, hnds⟩ := List.exists_cons_of_ne_nil (natDigits_ne_nil n.toNat)
  have hd : d.isDigit := natDigits_head_digit _ d (by rw [hnds]; rfl)
  have hval : valDigits 0 (d :: ds) = n.toNat := by rw [← hnds]; exact valDigits_natDigits _
  rw [hnds] at htake hdrop hfuel ⊢
  rw [parseFactor]
  refine ⟨?_⟩
  vcgen (errorOnMissingSpec := false)
  all_goals grind [Int.toNat_of_nonneg]

theorem not_digit_head_plus (mid : List Char) :
    ∀ c, ('+' :: mid).head? = some c → ¬ c.isDigit := by
  intro c hc
  simp only [List.head?_cons, Option.some.injEq] at hc
  subst hc
  simp [plus_not_digit _ rfl]

theorem not_digit_head_star (mid : List Char) :
    ∀ c, ('*' :: mid).head? = some c → ¬ c.isDigit := by
  intro c hc
  simp only [List.head?_cons, Option.some.injEq] at hc
  subst hc
  simp [star_not_digit _ rfl]

theorem not_digit_head_rparen (mid : List Char) :
    ∀ c, (')' :: mid).head? = some c → ¬ c.isDigit := by
  intro c hc
  simp only [List.head?_cons, Option.some.injEq] at hc
  subst hc
  simp [rparen_not_digit _ rfl]

theorem roundtrip (e : Expr) :
    (NonnegLits e → ∀ rest fuel,
      rest.head? ≠ some '+' → rest.head? ≠ some '*' →
      (∀ c, rest.head? = some c → ¬ c.isDigit) →
      (printExpr e ++ rest).length < fuel →
      ⦃ fun s => s = printExpr e ++ rest ⦄ parseExpr fuel ⦃ fun r s => r = e ∧ s = rest ⦄) ∧
    (NonnegLits e → ∀ rest fuel,
      rest.head? ≠ some '*' →
      (∀ c, rest.head? = some c → ¬ c.isDigit) →
      (printTerm e ++ rest).length < fuel →
      ⦃ fun s => s = printTerm e ++ rest ⦄ parseTerm fuel ⦃ fun r s => r = e ∧ s = rest ⦄) ∧
    (NonnegLits e → ∀ rest fuel,
      (∀ c, rest.head? = some c → ¬ c.isDigit) →
      (printFactor e ++ rest).length < fuel →
      ⦃ fun s => s = printFactor e ++ rest ⦄ parseFactor fuel ⦃ fun r s => r = e ∧ s = rest ⦄) := by
  induction e with
  | num n =>
    have hF : ∀ rest fuel, 0 ≤ n → (∀ c, rest.head? = some c → ¬ c.isDigit) →
        (natDigits n.toNat ++ rest).length < fuel →
        ⦃ fun s => s = natDigits n.toNat ++ rest ⦄ parseFactor fuel
        ⦃ fun r s => r = Expr.num n ∧ s = rest ⦄ :=
      fun rest fuel h0 hdig hfuel => core_F_num n h0 rest fuel hdig hfuel
    refine ⟨fun hnn rest fuel _ hstar hdig hfuel => ?_,
            fun hnn rest fuel hstar hdig hfuel => ?_,
            fun hnn rest fuel hdig hfuel => ?_⟩
    · exact core_E (.num n) _ rest fuel
        (core_T (.num n) _ rest fuel
          (hF rest fuel (by grind) hdig (by simpa [printExpr] using hfuel))
          (fun acc => termTail_stop rest fuel acc hstar))
        (fun acc => exprTail_stop rest fuel acc (by assumption))
    · exact core_T (.num n) _ rest fuel
        (hF rest fuel (by grind) hdig (by simpa [printTerm] using hfuel))
        (fun acc => termTail_stop rest fuel acc hstar)
    · exact hF rest fuel (by grind) hdig (by simpa [printFactor] using hfuel)
  | add a b iha ihb =>
    obtain ⟨-, ihaT, -⟩ := iha
    obtain ⟨-, ihbT, -⟩ := ihb
    have hE : NonnegLits (.add a b) → ∀ rest fuel,
        rest.head? ≠ some '+' → rest.head? ≠ some '*' →
        (∀ c, rest.head? = some c → ¬ c.isDigit) →
        (printExpr (.add a b) ++ rest).length < fuel →
        ⦃ fun s => s = printExpr (.add a b) ++ rest ⦄ parseExpr fuel
        ⦃ fun r s => r = Expr.add a b ∧ s = rest ⦄ := by
      intro hnn rest fuel hplus hstar hdig hfuel
      simp only [printExpr] at hfuel
      cases fuel with
      | zero => exact absurd hfuel (by simp)
      | succ f =>
        rw [show printExpr (a.add b) ++ rest
            = printTerm a ++ ('+' :: (printTerm b ++ rest)) from by
          simp [printExpr, List.append_assoc]]
        exact core_E_seq a b _ (printTerm b ++ rest) rest f
          (ihaT hnn.1 ('+' :: (printTerm b ++ rest)) (f + 1)
            (by simp) (not_digit_head_plus _) (by grind))
          (core_ET_step b (printTerm b ++ rest) rest f
            (ihbT hnn.2 rest f hstar hdig (by grind))
            (fun acc => exprTail_stop rest f acc hplus))
    have hF : NonnegLits (.add a b) → ∀ rest fuel,
        (∀ c, rest.head? = some c → ¬ c.isDigit) →
        (printFactor (.add a b) ++ rest).length < fuel →
        ⦃ fun s => s = printFactor (.add a b) ++ rest ⦄ parseFactor fuel
        ⦃ fun r s => r = Expr.add a b ∧ s = rest ⦄ := by
      intro hnn rest fuel hdig hfuel
      simp only [printFactor] at hfuel
      cases fuel with
      | zero => exact absurd hfuel (by simp)
      | succ f =>
        rw [show printFactor (a.add b) ++ rest
            = '(' :: (printExpr (a.add b) ++ (')' :: rest)) from by
          simp [printFactor, printExpr, List.append_assoc]]
        exact core_F_group (.add a b) _ rest f
          (hE hnn (')' :: rest) f (by simp) (by simp) (not_digit_head_rparen _)
            (by simp only [printExpr]; grind))
    have hT : NonnegLits (.add a b) → ∀ rest fuel,
        rest.head? ≠ some '*' →
        (∀ c, rest.head? = some c → ¬ c.isDigit) →
        (printTerm (.add a b) ++ rest).length < fuel →
        ⦃ fun s => s = printTerm (.add a b) ++ rest ⦄ parseTerm fuel
        ⦃ fun r s => r = Expr.add a b ∧ s = rest ⦄ := by
      intro hnn rest fuel hstar hdig hfuel
      exact core_T (.add a b) _ rest fuel
        (hF hnn rest fuel hdig (by simpa [printTerm, printFactor] using hfuel))
        (fun acc => termTail_stop rest fuel acc hstar)
    exact ⟨hE, hT, hF⟩
  | mul a b iha ihb =>
    obtain ⟨-, -, ihaF⟩ := iha
    obtain ⟨-, -, ihbF⟩ := ihb
    have hT : NonnegLits (.mul a b) → ∀ rest fuel,
        rest.head? ≠ some '*' →
        (∀ c, rest.head? = some c → ¬ c.isDigit) →
        (printTerm (.mul a b) ++ rest).length < fuel →
        ⦃ fun s => s = printTerm (.mul a b) ++ rest ⦄ parseTerm fuel
        ⦃ fun r s => r = Expr.mul a b ∧ s = rest ⦄ := by
      intro hnn rest fuel hstar hdig hfuel
      simp only [printTerm] at hfuel
      cases fuel with
      | zero => exact absurd hfuel (by simp)
      | succ f =>
        rw [show printTerm (a.mul b) ++ rest
            = printFactor a ++ ('*' :: (printFactor b ++ rest)) from by
          simp [printTerm, List.append_assoc]]
        exact core_T_seq a b _ (printFactor b ++ rest) rest f
          (ihaF hnn.1 ('*' :: (printFactor b ++ rest)) (f + 1)
            (not_digit_head_star _) (by grind))
          (core_TT_step b (printFactor b ++ rest) rest f
            (ihbF hnn.2 rest f hdig (by grind))
            (fun acc => termTail_stop rest f acc hstar))
    have hE : NonnegLits (.mul a b) → ∀ rest fuel,
        rest.head? ≠ some '+' → rest.head? ≠ some '*' →
        (∀ c, rest.head? = some c → ¬ c.isDigit) →
        (printExpr (.mul a b) ++ rest).length < fuel →
        ⦃ fun s => s = printExpr (.mul a b) ++ rest ⦄ parseExpr fuel
        ⦃ fun r s => r = Expr.mul a b ∧ s = rest ⦄ := by
      intro hnn rest fuel hplus hstar hdig hfuel
      exact core_E (.mul a b) _ rest fuel
        (hT hnn rest fuel hstar hdig (by simpa [printExpr, printTerm] using hfuel))
        (fun acc => exprTail_stop rest fuel acc hplus)
    have hF : NonnegLits (.mul a b) → ∀ rest fuel,
        (∀ c, rest.head? = some c → ¬ c.isDigit) →
        (printFactor (.mul a b) ++ rest).length < fuel →
        ⦃ fun s => s = printFactor (.mul a b) ++ rest ⦄ parseFactor fuel
        ⦃ fun r s => r = Expr.mul a b ∧ s = rest ⦄ := by
      intro hnn rest fuel hdig hfuel
      simp only [printFactor] at hfuel
      cases fuel with
      | zero => exact absurd hfuel (by simp)
      | succ f =>
        rw [show printFactor (a.mul b) ++ rest
            = '(' :: (printExpr (a.mul b) ++ (')' :: rest)) from by
          simp [printFactor, printExpr, List.append_assoc]]
        exact core_F_group (.mul a b) _ rest f
          (hE hnn (')' :: rest) f (by simp) (by simp) (not_digit_head_rparen _)
            (by simp only [printExpr]; grind))
    exact ⟨hE, hT, hF⟩

/-! ## Pure corollaries and the pipeline -/

/-- Parsing a printed expression consumes the whole input and returns the expression. -/
theorem parse_print_run (e : Expr) (h : NonnegLits e) :
    ((parseExpr ((printExpr e).length + 1)).run.run (printExpr e)).run
      = (.ok e, ([] : List Char)) := by
  have ht := (roundtrip e).1 h [] ((printExpr e).length + 1)
    (by simp) (by simp) (by simp) (by simp)
  have hw := ht.le_wp (printExpr e) (by simp)
  simp only [ExceptT.wp_apply_eq, StateT.wp_apply_eq] at hw
  rcases hres : ((parseExpr ((printExpr e).length + 1)).run.run (printExpr e)).run
    with ⟨err | r, s⟩
  · have hP := Id.of_wp_run_eq hres _ hw
    simp only [EPost.Cons.pushExcept] at hP
    have hb := Lean.Order.bot_le
      (α := EPost⟨String → List Char → Prop⟩) ⟨fun _ _ => False, EPost.Nil.mk⟩
    exact absurd (hb.1 err s hP) id
  · have hP := Id.of_wp_run_eq hres _ hw
    simp only [EPost.Cons.pushExcept] at hP
    obtain ⟨he, hs⟩ := hP
    rw [he, hs]

/-- Pure extraction of `compile_correct`. -/
theorem compile_correct_run (e : Expr) (s : List Int) :
    (((exec e.compile).run.run s).run : Except String Unit × List Int)
      = (.ok (), e.denote :: s) := by
  have hw := (compile_correct e s).le_wp s rfl
  simp only [ExceptT.wp_apply_eq, StateT.wp_apply_eq] at hw
  rcases hres : (((exec e.compile).run.run s).run : Except String Unit × List Int)
    with ⟨err | r, st⟩
  · have hP := Id.of_wp_run_eq hres _ hw
    simp only [EPost.Cons.pushExcept] at hP
    have hb := Lean.Order.bot_le
      (α := EPost⟨String → List Int → Prop⟩) ⟨fun _ _ => False, EPost.Nil.mk⟩
    exact absurd (hb.1 err st hP) id
  · have hP := Id.of_wp_run_eq hres _ hw
    simp only [EPost.Cons.pushExcept] at hP
    simp [hP]

/-- The full pipeline: parse the string, compile the expression, run the machine. -/
def evalString (input : String) : Except String Int :=
  match ((parseExpr (input.toList.length + 1)).run.run input.toList).run with
  | (.error msg, _) => .error msg
  | (.ok _, _ :: _) => .error "unexpected trailing input"
  | (.ok e, []) =>
    match ((exec e.compile).run.run []).run with
    | (.error msg, _) => .error msg
    | (.ok _, [v]) => .ok v
    | (.ok _, _) => .error "malformed final stack"

/-- Printing, parsing, compiling and executing an expression yields its denotation. -/
theorem evalString_print (e : Expr) (h : NonnegLits e) :
    evalString (String.ofList (printExpr e)) = .ok e.denote := by
  unfold evalString
  simp only [String.toList_ofList, parse_print_run e h, compile_correct_run]

/-! Sanity tests: parse trees, precedence, associativity, the pipeline, rejection. -/
example : ((parseExpr 10).run.run "1+2*3".toList).run
    = (.ok (Expr.add (.num 1) (.mul (.num 2) (.num 3))), []) := by cbv
example : ((parseExpr 10).run.run "(1+2)*3".toList).run
    = (.ok (Expr.mul (.add (.num 1) (.num 2)) (.num 3)), []) := by cbv
example : ((parseExpr 10).run.run "1+2+3".toList).run
    = (.ok (Expr.add (.add (.num 1) (.num 2)) (.num 3)), []) := by cbv
example : printExpr (.mul (.add (.num 1) (.num 2)) (.num 3)) = "(1+2)*3".toList := by cbv

example : evalString "1+2*3" = .ok 7 := by cbv
example : evalString "(1+2)*3" = .ok 9 := by cbv
example : evalString "12*(3+4)+5" = .ok 89 := by cbv
example : (evalString "1+").isOk = false := by cbv
example : (evalString "").isOk = false := by cbv
example : (evalString "1+2)").isOk = false := by cbv
