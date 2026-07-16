import Std.Internal.Do
import Std.Tactic.Do

/-!
# Edit distance by dynamic programming

`lev` is the textbook exponential recursion; `editDistance` is the two-row dynamic
program. The spec says they agree, so the DP is a verified memoization.

The alignment trick that makes the invariant one line: the outer loop consumes
`s.reverse`, so the processed part of `s` is `xs.prefix.reverse`, which grows by
*cons* at each step (`(P ++ [a]).reverse = a :: P.reverse`) and therefore matches
the front-peeling recursion of `lev` exactly. Rows are indexed by suffixes: the row
for a processed stem `sk` stores `lev sk (t.drop k)` at index `k`, and the inner
loop fills the new row right to left, peeling `t.drop (j-1) = t[j-1] :: t.drop j`
(`drop_step`). No reversal-symmetry theorem for `lev`, no `take`/prefix tables.

One derived rule carries the proof: `dpStep` says one inner iteration extends the
filled region of the new row down by one index; its proof is the three-way `min`
recurrence of `lev` against the three row reads, closed by `grind` after rewriting
with `drop_step`. `finish` then discharges every verification condition with four
seeds (`dpStep`, the `Array.ofFn` API for the initial row, and `List.drop_length`
for the base column).
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false
set_option linter.unusedVariables false

/-- Levenshtein distance, the executable specification. -/
def lev : List Char → List Char → Nat
  | [], t => t.length
  | _ :: s', [] => s'.length + 1
  | a :: s', b :: t' =>
    if a = b then lev s' t'
    else 1 + min (lev s' (b :: t')) (min (lev (a :: s') t') (lev s' t'))

@[grind =] theorem lev_nil_left (t : List Char) : lev [] t = t.length := by
  simp [lev]

@[grind =] theorem lev_nil_right (s : List Char) : lev s [] = s.length := by
  cases s <;> simp [lev]

@[grind =] theorem lev_cons_cons (a b : Char) (s' t' : List Char) :
    lev (a :: s') (b :: t') =
      if a = b then lev s' t'
      else 1 + min (lev s' (b :: t')) (min (lev (a :: s') t') (lev s' t')) := by
  rw [lev]

/-- Peeling the element at position `j` off the `j`-th suffix. -/
theorem drop_step {t : List Char} {j : Nat} (h : j < t.length) :
    t.drop j = t[j]! :: t.drop (j + 1) := by
  have := List.drop_eq_getElem_cons h
  grind

grind_pattern drop_step => List.drop j t

/-- Two-row dynamic program, filling right to left over suffixes of `t` while
consuming `s` from the back. -/
def editDistance (s t : List Char) : Id Nat := do
  let n := t.length
  let mut row : Array Nat := .ofFn (n := n + 1) (fun j => n - j.1)
  for a in s.reverse do
    let mut newRow := row.setIfInBounds n (row[n]! + 1)
    let mut j := n
    while 0 < j do
      j := j - 1
      let cost :=
        if t[j]! = a then row[j+1]!
        else 1 + min row[j]! (min newRow[j+1]! row[j+1]!)
      newRow := newRow.setIfInBounds j cost
    row := newRow
  return row[0]!

/-- One inner step extends the filled region of the new row down to `j - 1`. -/
theorem dpStep {t : List Char} {row newRow : Array Nat} {a : Char} {sk : List Char} {j : Nat}
    (hj : 0 < j) (hjle : j ≤ t.length)
    (hrs : row.size = t.length + 1) (hns : newRow.size = t.length + 1)
    (hrow : ∀ k, k ≤ t.length → row[k]! = lev sk (t.drop k))
    (hnew : ∀ k, j ≤ k → k ≤ t.length → newRow[k]! = lev (a :: sk) (t.drop k)) :
    ∀ k, j - 1 ≤ k → k ≤ t.length →
      (newRow.setIfInBounds (j - 1)
        (if t[j - 1]! = a then row[j - 1 + 1]!
         else min row[j - 1]! (min newRow[j - 1 + 1]! row[j - 1 + 1]!) + 1))[k]!
        = lev (a :: sk) (t.drop k) := by
  intro k hk1 hk2
  by_cases hkj : k = j - 1
  · rw [← hkj]
    have hlt : k < t.length := by omega
    have hd : t.drop k = t[k]! :: t.drop (k + 1) := drop_step hlt
    have hr1 := hrow (k + 1) (by omega)
    have hr0 := hrow k (by omega)
    have hn1 := hnew (k + 1) (by omega) (by omega)
    rw [hd, lev_cons_cons]
    grind
  · have hk : j ≤ k := by omega
    have := hnew k hk hk2
    grind

theorem editDistance_spec (s t : List Char) :
    ⦃ True ⦄ editDistance s t
    ⦃ fun r => r = lev s t ⦄ := by
  vcgen [editDistance] invariants
  | inv1 => fun xs row => row.size = t.length + 1 ∧
      ∀ k, k ≤ t.length → row[k]! = lev xs.prefix.reverse (t.drop k)
  | inv2 pref cur suff hsplit row0 hinv => fun st => match st with
    | .inl (newRow, j) => j ≤ t.length ∧ newRow.size = t.length + 1 ∧
        (∀ k, j ≤ k → k ≤ t.length → newRow[k]! = lev (cur :: pref.reverse) (t.drop k))
    | .inr (newRow, j) => newRow.size = t.length + 1 ∧
        (∀ k, k ≤ t.length → newRow[k]! = lev (cur :: pref.reverse) (t.drop k))
  | inv3 => fun st => st.2
  with finish [Array.size_ofFn, Array.getElem_ofFn, List.drop_length, dpStep]

/-! Sanity tests. `lev` reduces in the kernel; the program needs `native_decide`
(the `while` loop is an opaque fixpoint). -/
example : lev "kitten".toList "sitting".toList = 3 := by cbv
example : (editDistance "kitten".toList "sitting".toList).run = 3 := by native_decide
example : (editDistance "flaw".toList "lawn".toList).run = 2 := by native_decide
example : (editDistance [] []).run = 0 := by native_decide
example : (editDistance "abc".toList "abc".toList).run = 0 := by native_decide
example : (editDistance "abc".toList []).run = 3 := by native_decide
example : (editDistance [] "abc".toList).run = 3 := by native_decide
example : (editDistance "ab".toList "ba".toList).run = 2 := by native_decide
