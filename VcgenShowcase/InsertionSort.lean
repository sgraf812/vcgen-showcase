import Std.Internal.Do
import Std.Tactic.Do
import VcgenShowcase.RangeSplit

/-!
# In-place insertion sort

The flagship: a `while` loop nested in a `for` loop, mutating the array by swaps. The
spec is full correctness: the result is a permutation of the input and sorted.

The proof supplies three clauses: the outer invariant (sorted prefix), the inner
invariant (`.inl`: sorted up to the current index except at the insertion point;
`.inr`: sorted up to the current index), and the variant (the insertion point `j`).
Two seeds support `finish`: `range'_split_pos` (the split element of a `range'`
sits at start plus prefix length, needed because the outer range starts at `1` and
the position equation for a non-zero start is not derivable by e-matching) and
`perm_swapIfInBounds` (threading the permutation through a swap).

One verification condition survives `finish`: the loop-exit step at the insertion
point, where sortedness extends across `arr[j-1]! ≤ arr[j]!`. `case vc6` supplies
grind the invariant instantiated at `q` and its predecessor `q-1`, and grind closes
the arithmetic. `with (try finish)` plus a named `case` is the escape hatch for
exactly this situation. This is the direct, easy proof: handing grind the two
instantiations it cannot form on its own, since `arr[q-1]!` is not a ground term
until `q = j` is derived. Folding the inner sortedness into a named predicate with
a `@[grind]` lemma that exposes the predecessor step would let `finish` close this
case unaided, at the cost of a heavier invariant.

There is no `Manual` namespace here: the same-base baseline for this program is the
literal composition of the taxes demonstrated separately in `FindPair` (nested
loops), `TwoSum`/`Isqrt` (`while` as an opaque fixpoint), and `DutchFlag` (swap
reasoning and grind granularity), compounded by the position arithmetic of the
non-zero range start.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false
set_option linter.unusedVariables false

def insertionSort (a : Array Int) : Id (Array Int) := do
  let mut arr := a
  for i in [1:arr.size] do
    let mut j := i
    while 0 < j ∧ arr[j]! < arr[j-1]! do
      arr := arr.swapIfInBounds (j-1) j
      j := j - 1
  return arr


theorem insertionSort_spec (a : Array Int) :
    ⦃ True ⦄ insertionSort a
    ⦃ fun r => r.Perm a ∧ r.size = a.size ∧
        ∀ p q, p ≤ q → q < r.size → (r[p]! : Int) ≤ r[q]! ⦄ := by
  vcgen [insertionSort] invariants
  | inv1 => fun xs arr => arr.Perm a ∧ arr.size = a.size ∧
      (∀ p q, p ≤ q → q < 1 + xs.prefix.length → q < arr.size → (arr[p]! : Int) ≤ arr[q]!)
  | inv2 pref cur suff hsplit arr0 hinv => fun s => match s with
    | .inl (arr, j) => j ≤ cur ∧ cur < arr.size ∧ arr.Perm a ∧ arr.size = a.size ∧
        (∀ p q, p ≤ q → q ≤ cur → q ≠ j → (arr[p]! : Int) ≤ arr[q]!)
    | .inr (arr, j) => cur < arr.size ∧ arr.Perm a ∧ arr.size = a.size ∧
        (∀ p q, p ≤ q → q ≤ cur → (arr[p]! : Int) ≤ arr[q]!)
  | inv3 => fun s => s.2
  with (try finish [Array.Perm.refl])
  case vc6 =>
    rename_i s hinv hguard
    obtain ⟨arr, j⟩ := s
    obtain ⟨hj, hcur, hperm, hsz, hI⟩ := hinv
    refine ⟨hcur, hperm, hsz, fun p q hpq hq => ?_⟩
    have := hI p (q - 1)
    have := hI p q
    grind

/-! Sanity tests. -/
-- `native_decide`: the program does not reduce in the kernel (`repeatM.impl` is opaque).
example : (insertionSort #[3, 1, 2]).run = #[1, 2, 3] := by native_decide
example : (insertionSort #[5, 4, 3, 2, 1]).run = #[1, 2, 3, 4, 5] := by native_decide
example : (insertionSort #[]).run = #[] := by native_decide
example : (insertionSort #[7]).run = #[7] := by native_decide
example : (insertionSort #[1, 2, 3]).run = #[1, 2, 3] := by native_decide
example : (insertionSort #[2, 1, 2, 1]).run = #[1, 1, 2, 2] := by native_decide
example : (insertionSort #[0, -5, 3, -5]).run = #[-5, -5, 0, 3] := by native_decide

example : (insertionSort #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]).run =
    #[1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by native_decide
