import Std.Internal.Do
import Std.Tactic.Do

/-!
# Compiler correctness for a stack machine

Arithmetic expressions compile to instructions for a stack machine running in
`ExceptT String (StateM (List Int))`, throwing on stack underflow.

`compile_correct` states that executing compiled code pushes the denotation. The
omitted exception postcondition defaults to `⊥`, so the theorem also proves that
compiled code never underflows.

The proof is structural induction on the expression. In each case `exec_append`
reshapes the program into sequential composition, and `vcgen` composes the induction
hypotheses (passed as spec lemmas) through the binds; `finish` closes the arithmetic.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

inductive Expr where
  | num (n : Int)
  | add (e₁ e₂ : Expr)
  | mul (e₁ e₂ : Expr)

@[grind] def Expr.denote : Expr → Int
  | .num n => n
  | .add e₁ e₂ => e₁.denote + e₂.denote
  | .mul e₁ e₂ => e₁.denote * e₂.denote

inductive Instr where
  | push (n : Int)
  | add
  | mul

abbrev StackM := ExceptT String (StateM (List Int))

def execInstr : Instr → StackM Unit
  | .push n => modify (n :: ·)
  | .add => do
    match ← get with
    | y :: x :: st => set ((x + y) :: st)
    | _ => throw "stack underflow"
  | .mul => do
    match ← get with
    | y :: x :: st => set ((x * y) :: st)
    | _ => throw "stack underflow"

def exec : List Instr → StackM Unit
  | [] => pure ()
  | i :: is => do execInstr i; exec is

def Expr.compile : Expr → List Instr
  | .num n => [.push n]
  | .add e₁ e₂ => e₁.compile ++ e₂.compile ++ [.add]
  | .mul e₁ e₂ => e₁.compile ++ e₂.compile ++ [.mul]

theorem exec_append (xs ys : List Instr) :
    exec (xs ++ ys) = (do exec xs; exec ys) := by
  induction xs with
  | nil => simp [exec]
  | cons i is ih => simp [exec, ih]

theorem compile_correct (e : Expr) (s : List Int) :
    ⦃ fun st => st = s ⦄
    exec e.compile
    ⦃ fun _ st => st = e.denote :: s ⦄ := by
  induction e generalizing s with
  | num n =>
    simp only [Expr.compile]
    vcgen [exec, execInstr] with finish
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.compile, exec_append]
    vcgen [exec, execInstr, ih₁, ih₂] with finish
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.compile, exec_append]
    vcgen [exec, execInstr, ih₁, ih₂] with finish

namespace Manual

/-! The same theorem without `vcgen`, as a pure equation on the run of the transformer
stack: `run_seq` is the hand-derived sequencing rule, the per-instruction lemmas
evaluate single steps, and the induction mirrors the `vcgen` proof with the induction
hypotheses used as rewrite rules.

This is the mildest of the manual baselines, because the program is first-order
sequencing whose steps evaluate by `rfl`. Places to get stuck:

1. `run_seq` again has to exist before anything composes.
2. The per-instruction lemmas must fix the exact stack shape (`y :: x :: st`); the
   spec-level fact that compiled code always provides it is carried by the induction
   hypotheses' equations rather than checked by a tactic.
3. The rewrites must be `simp only`, not `rw`: each `run_seq` step leaves a
   `match (.ok …, …) with` redex that `rw` will not iota-reduce, and the next rewrite
   then fails to find its pattern.
-/

theorem StackM.run_seq {α β : Type} (x : StackM α) (k : α → StackM β) (st : List Int) :
    (((x >>= k).run.run st).run : Except String β × List Int) =
      match ((x.run.run st).run : Except String α × List Int) with
      | (.ok a, s) => (((k a).run.run s).run : Except String β × List Int)
      | (.error e, s) => (.error e, s) := by
  rcases h : ((x.run.run st).run : Except String α × List Int) with ⟨r | e, s⟩ <;>
    simp [ExceptT.run_bind, StateT.run_bind, h]

theorem execInstr_push (n : Int) (st : List Int) :
    (((execInstr (.push n)).run.run st).run : Except String Unit × List Int) =
      (.ok (), n :: st) := rfl

theorem execInstr_add (y x : Int) (st : List Int) :
    (((execInstr .add).run.run (y :: x :: st)).run : Except String Unit × List Int) =
      (.ok (), (x + y) :: st) := rfl

theorem execInstr_mul (y x : Int) (st : List Int) :
    (((execInstr .mul).run.run (y :: x :: st)).run : Except String Unit × List Int) =
      (.ok (), (x * y) :: st) := rfl

theorem exec_nil (st : List Int) :
    (((exec []).run.run st).run : Except String Unit × List Int) = (.ok (), st) := rfl

theorem exec_cons (i : Instr) (is : List Instr) :
    exec (i :: is) = (do execInstr i; exec is) := rfl

theorem compile_correct (e : Expr) (s : List Int) :
    (((exec e.compile).run.run s).run : Except String Unit × List Int) =
      (.ok (), e.denote :: s) := by
  induction e generalizing s with
  | num n =>
    simp only [Expr.compile, Expr.denote, exec_cons, StackM.run_seq, execInstr_push, exec_nil]
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.compile, Expr.denote, exec_append, exec_cons, StackM.run_seq,
      ih₁, ih₂, execInstr_add, exec_nil]
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.compile, Expr.denote, exec_append, exec_cons, StackM.run_seq,
      ih₁, ih₂, execInstr_mul, exec_nil]

end Manual

/-! Sanity tests. -/
example : (((exec (Expr.compile (.add (.num 2) (.mul (.num 3) (.num 4))))).run.run []).run
    : Except String Unit × List Int) = (.ok (), [14]) := by cbv
example : (((exec (Expr.compile (.num 7))).run.run []).run
    : Except String Unit × List Int) = (.ok (), [7]) := by cbv
example : (((exec (Expr.compile (.mul (.add (.num 1) (.num 2)) (.num 5)))).run.run []).run
    : Except String Unit × List Int) = (.ok (), [15]) := by cbv
example : (((exec [Instr.add]).run.run []).run
    : Except String Unit × List Int).1 = .error "stack underflow" := by cbv

/- The machine is not only a compilation target: hand-written programs run too. -/
example : (((exec [.push 1, .push 2, .add, .push 3, .mul]).run.run []).run
    : Except String Unit × List Int) = (.ok (), [9]) := by cbv

/- The compiler emits postfix order. -/
example : Expr.compile (.add (.num 1) (.mul (.num 2) (.num 3))) =
    [.push 1, .push 2, .push 3, .mul, .add] := by cbv
