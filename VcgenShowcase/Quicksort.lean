import Std.Internal.Do
import Std.Tactic.Do
import VcgenShowcase.RangeSplit

/-!
# In-place quicksort

Lomuto partition in a `for` loop, recursion on explicit fuel, full functional
correctness: the result is a sorted permutation of the input.

Structure:

* The slice toolkit. `extract_perm` restricts a whole-array permutation with an
  equal-outside guarantee to permuted slices (append cancellation on the
  three-piece `extract` decomposition), and `range_bound_transfer` moves any
  pointwise bound on a range across such a permutation. These two lemmas are what
  let the recursion own its subrange: each recursive call reports only
  "permutation of the whole array, untouched outside my range, sorted inside",
  and the caller transports the partition bounds through it.
* `partition` with `PartInv`, a zone invariant in the style of `DutchFlag`; each
  transition is a dedicated lemma and the loop-level residue is index arithmetic
  from `range'_split_pos`.
* `qsortAux` recurses on fuel; the spec is one induction over fuel where `vcgen`
  consumes `partition_spec` and the induction hypothesis as spec lemmas, and
  `qs_compose` (the only real content: stitching two sorted halves around the
  pivot) closes the recursive case via `finish`.

`QSPost` and `PartPost` carry `grind_pattern` equations for their definitions;
without them, `finish` cannot project the conjuncts and even the size side
conditions of the recursive calls survive.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false
set_option linter.unusedVariables false

/-! ## Slice toolkit: transferring range-local facts across whole-array permutations -/

/-- Any array splits at two cut points. -/
theorem extract_decomp (x : Array Int) {lo hi : Nat} (hlo : lo ≤ hi) (hhi : hi ≤ x.size) :
    x = x.extract 0 lo ++ x.extract lo hi ++ x.extract hi x.size := by
  rw [Array.extract_append_extract,
    show min 0 lo = 0 from by omega, show max lo hi = hi from by omega,
    Array.extract_append_extract,
    show min 0 hi = 0 from by omega, show max hi x.size = x.size from by omega]
  simp

/-- Equal-outside whole-array permutations restrict to permuted slices. -/
theorem extract_perm {a r : Array Int} {lo hi : Nat}
    (hperm : r.Perm a) (hsz : r.size = a.size) (hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (hout : ∀ k, k < lo ∨ hi ≤ k → r[k]! = a[k]!) :
    (r.extract lo hi).Perm (a.extract lo hi) := by
  have h1 : r.extract 0 lo = a.extract 0 lo := by
    apply Array.ext
    · grind
    · intro i hi1 hi2
      have hb : i < r.size := by grind
      have := hout i (Or.inl (by grind))
      rw [getElem!_pos, getElem!_pos] at this <;> grind
  have h2 : r.extract hi r.size = a.extract hi a.size := by
    apply Array.ext
    · grind
    · intro i hi1 hi2
      have hb : hi + i < r.size := by grind
      have := hout (hi + i) (Or.inr (by omega))
      rw [getElem!_pos, getElem!_pos] at this <;> grind
  have hd := extract_decomp r (lo := lo) (hi := hi) hlo (by omega)
  have hd' := extract_decomp a (lo := lo) (hi := hi) hlo hhi
  rw [hd, hd', h1, h2] at hperm
  have hl := Array.perm_iff_toList_perm.mp hperm
  simp only [Array.toList_append] at hl
  rw [List.append_assoc, List.append_assoc] at hl
  have hm := (List.perm_append_left_iff _).mp hl
  have hm2 := (List.perm_append_right_iff _).mp hm
  exact Array.perm_iff_toList_perm.mpr hm2

/-- A pointwise bound on a range survives any equal-outside permutation. -/
theorem range_bound_transfer {a r : Array Int} {lo hi : Nat} {P : Int → Prop}
    (hperm : r.Perm a) (hsz : r.size = a.size) (hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (hout : ∀ k, k < lo ∨ hi ≤ k → r[k]! = a[k]!)
    (hbound : ∀ k, lo ≤ k → k < hi → P a[k]!) :
    ∀ k, lo ≤ k → k < hi → P r[k]! := by
  intro k hk1 hk2
  have hep := extract_perm hperm hsz hlo hhi hout
  have hmem : r[k]! ∈ (r.extract lo hi) := by
    have : (r.extract lo hi)[k - lo]! = r[k]! := by grind
    rw [← this]
    have hsz' : k - lo < (r.extract lo hi).size := by grind
    grind [Array.getElem_mem]
  have hmem' : r[k]! ∈ (a.extract lo hi) := hep.mem_iff.mp hmem
  obtain ⟨j, hj, hje⟩ := Array.mem_iff_getElem.mp hmem'
  have hjs : j < (a.extract lo hi).size := hj
  have : (a.extract lo hi)[j] = a[lo + j]! := by grind
  rw [this] at hje
  have := hbound (lo + j) (by omega) (by grind)
  rw [hje] at this
  exact this

/-! ## Partition -/

/-- What partition guarantees: a pivot position `mid` splitting `[lo, hi)` into
strictly-below and at-least zones, everything outside untouched. -/
def PartPost (a : Array Int) (lo hi : Nat) (r : Array Int) (mid : Nat) : Prop :=
  r.size = a.size ∧ r.Perm a ∧ lo ≤ mid ∧ mid < hi ∧
  (∀ k, k < lo ∨ hi ≤ k → r[k]! = a[k]!) ∧
  (∀ k, lo ≤ k → k < mid → r[k]! < r[mid]!) ∧
  (∀ k, mid < k → k < hi → r[mid]! ≤ r[k]!)

/-- Lomuto partition of `[lo, hi)` with pivot `a[hi-1]!`. -/
def partition (a : Array Int) (lo hi : Nat) : Id (Array Int × Nat) := do
  let pivot := a[hi-1]!
  let mut arr := a
  let mut mid := lo
  for i in [lo:hi-1] do
    if arr[i]! < pivot then
      arr := arr.swapIfInBounds mid i
      mid := mid + 1
  arr := arr.swapIfInBounds mid (hi-1)
  return (arr, mid)

/-- The partition loop invariant at cursor position `i`. -/
def PartInv (a : Array Int) (lo hi : Nat) (arr : Array Int) (mid i : Nat) : Prop :=
  arr.size = a.size ∧ arr.Perm a ∧ lo ≤ mid ∧ mid ≤ i ∧
  (∀ k, k < lo ∨ hi ≤ k → arr[k]! = a[k]!) ∧
  (∀ k, lo ≤ k → k < mid → arr[k]! < a[hi-1]!) ∧
  (∀ k, mid ≤ k → k < i → a[hi-1]! ≤ arr[k]!) ∧
  arr[hi-1]! = a[hi-1]!

theorem partInv_init (a : Array Int) (lo hi j : Nat) (hj : lo = j) :
    PartInv a lo hi a lo j := by
  subst hj
  refine ⟨rfl, Array.Perm.refl _, Nat.le_refl _, Nat.le_refl _,
    fun k _ => rfl, fun k h1 h2 => by omega, fun k h1 h2 => by omega, rfl⟩

theorem partInv_step_lt {a arr : Array Int} {lo hi mid i j : Nat}
    (h : PartInv a lo hi arr mid i) (hlo : lo ≤ i) (hup : i < hi - 1) (hhi : hi ≤ a.size)
    (hlt : arr[i]! < a[hi-1]!) (hj : i + 1 = j) :
    PartInv a lo hi (arr.swapIfInBounds mid i) (mid + 1) j := by
  subst hj
  obtain ⟨hsz, hperm, hm1, hm2, hout, hzlt, hzge, hpiv⟩ := h
  have hmb : mid < arr.size := by omega
  have hib : i < arr.size := by omega
  refine ⟨by grind, perm_swapIfInBounds hmb hib hperm, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hkm : k ≠ mid := by omega
    have hki : k ≠ i := by omega
    grind
  · intro k h1 h2
    by_cases hkm : k = mid
    · grind
    · have := hzlt k h1 (by omega)
      grind
  · intro k h1 h2
    by_cases hki : k = i
    · by_cases hmi : mid = i
      · grind
      · have := hzge mid (Nat.le_refl _) (by omega)
        grind
    · have := hzge k (by omega) (by omega)
      grind
  · have hne1 : hi - 1 ≠ mid := by omega
    have hne2 : hi - 1 ≠ i := by omega
    grind

theorem partInv_step_ge {a arr : Array Int} {lo hi mid i j : Nat}
    (h : PartInv a lo hi arr mid i) (hup : i < hi - 1)
    (hge : ¬ arr[i]! < a[hi-1]!) (hj : i + 1 = j) :
    PartInv a lo hi arr mid j := by
  subst hj
  obtain ⟨hsz, hperm, hm1, hm2, hout, hzlt, hzge, hpiv⟩ := h
  refine ⟨hsz, hperm, hm1, by omega, hout, hzlt, ?_, hpiv⟩
  intro k h1 h2
  by_cases hki : k = i
  · subst hki; omega
  · exact hzge k h1 (by omega)

theorem partInv_final {a arr : Array Int} {lo hi mid i : Nat}
    (h : PartInv a lo hi arr mid i) (hi1 : i = hi - 1) (hlo : lo < hi) (hhi : hi ≤ a.size) :
    PartPost a lo hi (arr.swapIfInBounds mid (hi - 1)) mid := by
  subst hi1
  obtain ⟨hsz, hperm, hm1, hm2, hout, hzlt, hzge, hpiv⟩ := h
  have hmb : mid < arr.size := by omega
  have hhb : hi - 1 < arr.size := by omega
  have hmidv : (arr.swapIfInBounds mid (hi - 1))[mid]! = a[hi-1]! := by grind
  refine ⟨by grind, perm_swapIfInBounds hmb hhb hperm, hm1, by omega, ?_, ?_, ?_⟩
  · intro k hk
    have h1 : k ≠ mid := by omega
    have h2 : k ≠ hi - 1 := by omega
    grind
  · intro k h1 h2
    rw [hmidv]
    have hne1 : k ≠ mid := by omega
    have hne2 : k ≠ hi - 1 := by omega
    have := hzlt k h1 h2
    grind
  · intro k h1 h2
    rw [hmidv]
    by_cases hk : k = hi - 1
    · by_cases hmi : mid = hi - 1
      · omega
      · have := hzge mid (Nat.le_refl _) (by omega)
        grind
    · have hne : k ≠ mid := by omega
      have := hzge k (by omega) (by omega)
      grind

theorem partition_spec (a : Array Int) (lo hi : Nat) (hlo : lo < hi) (hhi : hi ≤ a.size) :
    ⦃ True ⦄ partition a lo hi
    ⦃ fun r => PartPost a lo hi r.1 r.2 ⦄ := by
  vcgen [partition] invariants
  | inv1 => fun xs (arr, mid) => PartInv a lo hi arr mid (lo + xs.prefix.length) ∧
      lo + xs.prefix.length ≤ hi - 1
  with finish [partInv_init, partInv_step_lt, partInv_step_ge, partInv_final,
    range'_split_pos]

/-! ## Quicksort -/

/-- What sorting `[lo, hi)` in place guarantees. -/
def QSPost (a : Array Int) (lo hi : Nat) (r : Array Int) : Prop :=
  r.size = a.size ∧ r.Perm a ∧ (∀ k, k < lo ∨ hi ≤ k → r[k]! = a[k]!) ∧
  (∀ p q, lo ≤ p → p ≤ q → q < hi → r[p]! ≤ r[q]!)

theorem qsPost_def (a : Array Int) (lo hi : Nat) (r : Array Int) :
    QSPost a lo hi r = (r.size = a.size ∧ r.Perm a ∧
      (∀ k, k < lo ∨ hi ≤ k → r[k]! = a[k]!) ∧
      (∀ p q, lo ≤ p → p ≤ q → q < hi → r[p]! ≤ r[q]!)) := rfl

grind_pattern qsPost_def => QSPost a lo hi r

theorem partPost_def (a : Array Int) (lo hi : Nat) (r : Array Int) (mid : Nat) :
    PartPost a lo hi r mid = (r.size = a.size ∧ r.Perm a ∧ lo ≤ mid ∧ mid < hi ∧
      (∀ k, k < lo ∨ hi ≤ k → r[k]! = a[k]!) ∧
      (∀ k, lo ≤ k → k < mid → r[k]! < r[mid]!) ∧
      (∀ k, mid < k → k < hi → r[mid]! ≤ r[k]!)) := rfl

grind_pattern partPost_def => PartPost a lo hi r mid

def qsortAux : Nat → Array Int → Nat → Nat → Id (Array Int)
  | 0, a, _, _ => pure a
  | fuel + 1, a, lo, hi => do
    if hi ≤ lo + 1 then
      pure a
    else
      let (a₁, mid) ← partition a lo hi
      let a₂ ← qsortAux fuel a₁ lo mid
      let a₃ ← qsortAux fuel a₂ (mid + 1) hi
      pure a₃

/-- Stitching a partition and two sorted halves into a sorted range. -/
theorem qs_compose {a a₁ a₂ a₃ : Array Int} {lo mid hi : Nat}
    (hhi : hi ≤ a.size)
    (hpart : PartPost a lo hi a₁ mid)
    (hL : QSPost a₁ lo mid a₂)
    (hR : QSPost a₂ (mid + 1) hi a₃) :
    QSPost a lo hi a₃ := by
  obtain ⟨hsz1, hperm1, hm1, hm2, hout1, hlt1, hge1⟩ := hpart
  obtain ⟨hsz2, hperm2, hout2, hsort2⟩ := hL
  obtain ⟨hsz3, hperm3, hout3, hsort3⟩ := hR
  have hout31 : ∀ k, k ≤ mid → a₃[k]! = a₂[k]! := fun k hk => hout3 k (Or.inl (by omega))
  have hpv2 : a₂[mid]! = a₁[mid]! := hout2 mid (Or.inr (Nat.le_refl _))
  have hpv3 : a₃[mid]! = a₁[mid]! := by rw [hout31 mid (Nat.le_refl _), hpv2]
  have hL2 : ∀ k, lo ≤ k → k < mid → a₂[k]! < a₁[mid]! :=
    range_bound_transfer (P := (· < a₁[mid]!)) hperm2 hsz2 (by omega) (by omega) hout2 hlt1
  have hL3 : ∀ k, lo ≤ k → k < mid → a₃[k]! < a₁[mid]! := fun k h1 h2 => by
    rw [hout31 k (by omega)]; exact hL2 k h1 h2
  have hR2 : ∀ k, mid + 1 ≤ k → k < hi → a₁[mid]! ≤ a₂[k]! := fun k h1 h2 => by
    rw [hout2 k (Or.inr (by omega))]; exact hge1 k (by omega) h2
  have hR3 : ∀ k, mid + 1 ≤ k → k < hi → a₁[mid]! ≤ a₃[k]! :=
    range_bound_transfer (P := (a₁[mid]! ≤ ·)) hperm3 hsz3 (by omega) (by omega) hout3 hR2
  refine ⟨by omega, hperm3.trans (hperm2.trans hperm1), ?_, ?_⟩
  · intro k hk
    rw [hout3 k (by omega), hout2 k (by omega), hout1 k hk]
  · intro p q hp hpq hq
    rcases Nat.lt_or_ge q mid with hqm | hqm
    · rw [hout31 p (by omega), hout31 q (by omega)]
      exact hsort2 p q hp hpq hqm
    · rcases Nat.eq_or_lt_of_le hqm with rfl | hqm'
      · rcases Nat.eq_or_lt_of_le hpq with rfl | hpm
        · exact Int.le_refl _
        · rw [hpv3]
          exact Int.le_of_lt (hL3 p hp hpm)
      · rcases Nat.lt_or_ge p mid with hpm | hpm
        · exact Int.le_of_lt (Int.lt_of_lt_of_le (hL3 p hp hpm) (hR3 q (by omega) hq))
        · rcases Nat.eq_or_lt_of_le hpm with hpe | hpm'
          · rw [← hpe, hpv3]
            exact hR3 q (by omega) hq
          · exact hsort3 p q (by omega) hpq hq

theorem qsortAux_spec (fuel : Nat) :
    ∀ (a : Array Int) (lo hi : Nat), hi ≤ a.size → hi - lo ≤ fuel →
    ⦃ True ⦄ qsortAux fuel a lo hi ⦃ fun r => QSPost a lo hi r ⦄ := by
  induction fuel with
  | zero =>
    intro a lo hi hhi hfuel
    rw [qsortAux]
    vcgen
    refine ⟨rfl, Array.Perm.refl _, fun k _ => rfl, fun p q h1 h2 h3 => ?_⟩
    omega
  | succ fuel ih =>
    intro a lo hi hhi hfuel
    rw [qsortAux]
    vcgen [partition_spec, ih] with finish [qs_compose, Array.Perm.refl]

def quicksort (a : Array Int) : Id (Array Int) :=
  qsortAux a.size a 0 a.size

theorem quicksort_spec (a : Array Int) :
    ⦃ True ⦄ quicksort a
    ⦃ fun r => r.Perm a ∧ r.size = a.size ∧
        ∀ p q, p ≤ q → q < r.size → r[p]! ≤ r[q]! ⦄ := by
  vcgen [quicksort, qsortAux_spec] with finish

/-! Sanity tests. `native_decide`: loops and fuel recursion. -/
example : (quicksort #[3, 1, 2]).run = #[1, 2, 3] := by native_decide
example : (quicksort #[5, 4, 3, 2, 1]).run = #[1, 2, 3, 4, 5] := by native_decide
example : (quicksort #[]).run = #[] := by native_decide
example : (quicksort #[7]).run = #[7] := by native_decide
example : (quicksort #[2, 1, 2, 1]).run = #[1, 1, 2, 2] := by native_decide
example : (quicksort #[0, -5, 3, -5]).run = #[-5, -5, 0, 3] := by native_decide
example : (quicksort #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]).run
    = #[1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by native_decide
