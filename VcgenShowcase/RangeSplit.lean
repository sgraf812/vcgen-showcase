import Std.Internal.Do
import Std.Tactic.Do

/-!
# Shared seed rules for loop verification conditions

Loop VCs over `for i in [s:n]` see the iteration cursor as a split
`List.range' s n = pref ++ c :: suff`. For a non-zero start, the position of the
split element and the interval reading of the prefix are not derivable by e-matching
from the built-in `range'` rules; the two `range'` lemmas provide them, triggered on
the split's subterms. `perm_swapIfInBounds` threads an `Array.Perm` through an
in-bounds swap, triggered on the swapped array.
-/

/-- The split element of a `range'` sits at the start plus the prefix length. -/
theorem range'_split_pos {s n : Nat} {pref suff : List Nat} {c : Nat}
    (h : List.range' s n = pref ++ c :: suff) : c = s + pref.length := by
  have := List.eq_of_range'_eq_append_cons h
  omega

grind_pattern range'_split_pos => List.range' s n, pref ++ c :: suff

/-- Membership in the prefix of a `range'` split is interval membership. -/
theorem range'_split_mem_prefix {s n : Nat} {pref suff : List Nat} {c q : Nat}
    (h : List.range' s n = pref ++ c :: suff) : q ∈ pref ↔ (s ≤ q ∧ q < c) := by
  obtain ⟨k, hk, hpref, -⟩ := List.range'_eq_append_iff.mp (by simpa using h)
  have hc := range'_split_pos h
  subst hpref
  simp only [List.mem_range'_1, List.length_range'] at hc ⊢
  omega

grind_pattern range'_split_mem_prefix => List.range' s n, pref ++ c :: suff, q ∈ pref

/-- Swapping in bounds preserves any permutation relation to a fixed array. -/
theorem perm_swapIfInBounds {α : Type _} {xs l : Array α} {i j : Nat}
    (hi : i < xs.size) (hj : j < xs.size) (h : xs.Perm l) :
    (xs.swapIfInBounds i j).Perm l := by
  rw [Array.swapIfInBounds_def, dif_pos hi, dif_pos hj]
  exact (Array.swap_perm hi hj).trans h

grind_pattern perm_swapIfInBounds => (xs.swapIfInBounds i j).Perm l
