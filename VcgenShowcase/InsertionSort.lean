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

One verification condition survives `finish`: the loop-exit step, whose content is
the transitivity chain `arr[p]! ≤ arr[j-1]! ≤ arr[j]!` closing the gap at the
insertion point. grind does not find the chain even with `Int.le_trans` as a seed;
`case vc6` closes it in fifteen lines. `with (try finish)` plus a named `case` is
the escape hatch for exactly this situation.

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
    dsimp only at hguard ⊢
    obtain ⟨hj, hcur, hperm, hsz, hI⟩ := hinv
    refine ⟨hcur, hperm, hsz, ?_⟩
    intro p q hpq hq
    by_cases hqj : q = j
    · subst hqj
      rcases Nat.eq_zero_or_pos q with hq0 | hpos
      · have hp0 : p = 0 := by omega
        rw [hp0, hq0]
        exact Int.le_refl _
      · have hge : ¬ ((arr[q]! : Int) < arr[q - 1]!) := fun h => hguard ⟨hpos, h⟩
        by_cases hpj : p = q
        · rw [hpj]
          exact Int.le_refl _
        · have h1 : (arr[p]! : Int) ≤ arr[q - 1]! := hI p (q - 1) (by omega) (by omega) (by omega)
          omega
    · exact hI p q hpq hq hqj
