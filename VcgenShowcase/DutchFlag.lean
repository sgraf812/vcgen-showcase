import Std.Internal.Do
import Std.Tactic.Do
import VcgenShowcase.ManualLoop

/-!
# Dutch national flag

In-place three-way partition around zero: a `while` loop over four mutable variables
(the array and three zone boundaries), swapping via `Array.swapIfInBounds`. The spec:
the result is a permutation of the input and splits into a negative, a zero, and a
positive zone.

The `vcgen` proof supplies the zone invariant and the variant `hi - mid`; `finish`
closes every verification condition on the `swapIfInBounds` grind API, with
`perm_swapIfInBounds` as the one derived rule (triggered on the swapped array) that
threads the permutation through the loop.

`Manual.dutchFlag_correct` is the same-base baseline on the `wrap`/`loop_forIn_eq`
machinery from `ManualLoop`. Places to get stuck, beyond those in `Isqrt.Manual` and
`TwoSum.Manual`:

1. Granularity of automation calls becomes the proof's load-bearing decision: handing
   one grind the whole packaged invariant preservation (size, permutation, bounds,
   three quantified zones, one swap) diverges even at five times the heartbeat
   budget, while the same facts split into per-zone step lemmas with destructured
   hypotheses close instantly. The `vcgen` proof hands `finish` the same content in
   one clause and never faces the choice.
2. The aux conclusion must be a single predicate application (`DFPost`): spelling the
   result's four projections separately makes the induction-hypothesis application
   time out in unification.
3. The equation hypotheses of the abstracted body must be cleared before the pure
   reasoning starts, or grind instantiates them at derived terms and diverges.
4. Tactic holes elaborate before the surrounding anonymous constructor assigns the
   existential witnesses, so `by omega` for the zone bounds sees unassigned
   metavariables; the closing term must be built with the facts composed by hand
   (`Nat.le_trans`, `hmh ▸ hk1`).
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

def dutchFlag (a : Array Int) : Id (Array Int) := do
  let mut arr := a
  let mut lo := 0
  let mut mid := 0
  let mut hi := arr.size
  while mid < hi do
    if arr[mid]! < 0 then
      arr := arr.swapIfInBounds lo mid
      lo := lo + 1
      mid := mid + 1
    else if arr[mid]! = 0 then
      mid := mid + 1
    else
      hi := hi - 1
      arr := arr.swapIfInBounds mid hi
  return arr

/-- Swapping in bounds preserves any permutation relation to a fixed array. -/
theorem perm_swapIfInBounds {xs l : Array α} {i j : Nat}
    (hi : i < xs.size) (hj : j < xs.size) (h : xs.Perm l) :
    (xs.swapIfInBounds i j).Perm l := by
  rw [Array.swapIfInBounds_def, dif_pos hi, dif_pos hj]
  exact (Array.swap_perm hi hj).trans h

grind_pattern perm_swapIfInBounds => (xs.swapIfInBounds i j).Perm l

theorem dutchFlag_spec (a : Array Int) :
    ⦃ True ⦄ dutchFlag a
    ⦃ fun r => r.size = a.size ∧ r.Perm a ∧
        ∃ p q : Nat, p ≤ q ∧ q ≤ r.size ∧
          (∀ k, k < p → (r[k]! : Int) < 0) ∧
          (∀ k, p ≤ k → k < q → (r[k]! : Int) = 0) ∧
          (∀ k, q ≤ k → k < r.size → (0 : Int) < r[k]!) ⦄ := by
  vcgen [dutchFlag] invariants
  | inv1 => fun s => match s with
    | .inl (arr, lo, mid, hi) =>
        arr.size = a.size ∧ arr.Perm a ∧
        lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ arr.size ∧
        (∀ k, k < lo → arr[k]! < 0) ∧
        (∀ k, lo ≤ k → k < mid → arr[k]! = 0) ∧
        (∀ k, hi ≤ k → k < arr.size → 0 < arr[k]!)
    | .inr (arr, lo, mid, hi) =>
        arr.size = a.size ∧ arr.Perm a ∧
        lo ≤ mid ∧ hi ≤ mid ∧ mid ≤ hi ∧ hi ≤ arr.size ∧
        (∀ k, k < lo → arr[k]! < 0) ∧
        (∀ k, lo ≤ k → k < mid → arr[k]! = 0) ∧
        (∀ k, hi ≤ k → k < arr.size → 0 < arr[k]!)
  | inv2 => fun s => s.2.2.2 - s.2.2.1
  with finish [Array.Perm.refl]

namespace Manual

set_option linter.unusedVariables false

@[grind] def DFInv (a arr : Array Int) (lo mid hi : Nat) : Prop :=
  arr.size = a.size ∧ arr.Perm a ∧ lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ arr.size ∧
  (∀ k, k < lo → (arr[k]! : Int) < 0) ∧
  (∀ k, lo ≤ k → k < mid → (arr[k]! : Int) = 0) ∧
  (∀ k, hi ≤ k → k < arr.size → (0 : Int) < arr[k]!)

/-- The loop exit condition of `dutchFlag`. -/
@[grind] def DFPost (a : Array Int) : Array Int × Nat × Nat × Nat → Prop
  | (arr, lo, mid, hi) => DFInv a arr lo mid hi ∧ mid = hi

private theorem step_neg {a arr : Array Int} {lo mid hi : Nat}
    (hinv : DFInv a arr lo mid hi) (hg : mid < hi) (hx : (arr[mid]! : Int) < 0) :
    DFInv a (arr.swapIfInBounds lo mid) (lo + 1) (mid + 1) hi := by
  obtain ⟨hsz, hperm, h1, h2, h3, hz1, hz2, hz3⟩ := hinv
  have hlo : lo < arr.size := by omega
  have hmid : mid < arr.size := by omega
  refine ⟨by simpa using hsz, perm_swapIfInBounds hlo hmid hperm, by omega, by omega,
    by simpa using h3, ?_, ?_, ?_⟩
  · intro k hk
    grind
  · intro k hk1 hk2
    grind
  · intro k hk1 hk2
    grind

private theorem step_zero {a arr : Array Int} {lo mid hi : Nat}
    (hinv : DFInv a arr lo mid hi) (hg : mid < hi) (hx : (arr[mid]! : Int) = 0) :
    DFInv a arr lo (mid + 1) hi := by
  obtain ⟨hsz, hperm, h1, h2, h3, hz1, hz2, hz3⟩ := hinv
  exact ⟨hsz, hperm, by omega, by omega, h3, hz1, by grind, hz3⟩

private theorem step_pos {a arr : Array Int} {lo mid hi : Nat}
    (hinv : DFInv a arr lo mid hi) (hg : mid < hi)
    (hx1 : ¬ (arr[mid]! : Int) < 0) (hx2 : ¬ (arr[mid]! : Int) = 0) :
    DFInv a (arr.swapIfInBounds mid (hi - 1)) lo mid (hi - 1) := by
  obtain ⟨hsz, hperm, h1, h2, h3, hz1, hz2, hz3⟩ := hinv
  have hmid : mid < arr.size := by omega
  have hhi : hi - 1 < arr.size := by omega
  refine ⟨by simpa using hsz, perm_swapIfInBounds hmid hhi hperm, by omega, by omega,
    by simpa using by omega, ?_, ?_, ?_⟩
  · intro k hk
    grind
  · intro k hk1 hk2
    grind
  · intro k hk1 hk2
    grind

private theorem loop_aux (a : Array Int)
    (F : (Array Int × Nat × Nat × Nat) → Id ((Array Int × Nat × Nat × Nat) ⊕ (Array Int × Nat × Nat × Nat)))
    (hneg : ∀ arr lo mid hi, mid < hi → (arr[mid]! : Int) < 0 →
      F (arr, lo, mid, hi) = pure (Sum.inl (arr.swapIfInBounds lo mid, lo + 1, mid + 1, hi)))
    (hzero : ∀ arr lo mid hi, mid < hi → ¬ (arr[mid]! : Int) < 0 → (arr[mid]! : Int) = 0 →
      F (arr, lo, mid, hi) = pure (Sum.inl (arr, lo, mid + 1, hi)))
    (hpos : ∀ arr lo mid hi, mid < hi → ¬ (arr[mid]! : Int) < 0 → ¬ (arr[mid]! : Int) = 0 →
      F (arr, lo, mid, hi) = pure (Sum.inl (arr.swapIfInBounds mid (hi - 1), lo, mid, hi - 1)))
    (hstop : ∀ arr lo mid hi, ¬ mid < hi →
      F (arr, lo, mid, hi) = pure (Sum.inr (arr, lo, mid, hi))) :
    ∀ fuel arr lo mid hi, hi - mid ≤ fuel → DFInv a arr lo mid hi →
      DFPost a (repeatM (m := Id) F (arr, lo, mid, hi)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro arr lo mid hi hfuel hinv
    have hguard : ¬ mid < hi := by omega
    rw [repeatM_eq_of_monadTail]
    simp only [repeatM.body, hstop arr lo mid hi hguard, pure_bind]
    refine ⟨hinv, ?_⟩
    obtain ⟨-, -, -, h4, -⟩ := hinv
    omega
  | succ fuel ih =>
    intro arr lo mid hi hfuel hinv
    rw [repeatM_eq_of_monadTail]
    by_cases hguard : mid < hi
    · by_cases hneg' : (arr[mid]! : Int) < 0
      · simp only [repeatM.body, hneg arr lo mid hi hguard hneg', pure_bind]
        clear hneg hzero hpos hstop
        exact ih (arr.swapIfInBounds lo mid) (lo + 1) (mid + 1) hi (by omega)
          (step_neg hinv hguard hneg')
      · by_cases hzero' : (arr[mid]! : Int) = 0
        · simp only [repeatM.body, hzero arr lo mid hi hguard hneg' hzero', pure_bind]
          clear hneg hzero hpos hstop
          exact ih arr lo (mid + 1) hi (by omega) (step_zero hinv hguard hzero')
        · simp only [repeatM.body, hpos arr lo mid hi hguard hneg' hzero', pure_bind]
          clear hneg hzero hpos hstop
          exact ih (arr.swapIfInBounds mid (hi - 1)) lo mid (hi - 1) (by omega)
            (step_pos hinv hguard hneg' hzero')
    · simp only [repeatM.body, hstop arr lo mid hi hguard, pure_bind]
      refine ⟨hinv, ?_⟩
      obtain ⟨-, -, -, h4, -⟩ := hinv
      omega

theorem dutchFlag_correct (a : Array Int) :
    (dutchFlag a).run.size = a.size ∧ (dutchFlag a).run.Perm a ∧
    ∃ p q : Nat, p ≤ q ∧ q ≤ (dutchFlag a).run.size ∧
      (∀ k, k < p → ((dutchFlag a).run[k]! : Int) < 0) ∧
      (∀ k, p ≤ k → k < q → ((dutchFlag a).run[k]! : Int) = 0) ∧
      (∀ k, q ≤ k → k < (dutchFlag a).run.size → (0 : Int) < (dutchFlag a).run[k]!) := by
  unfold dutchFlag
  simp only [loop_forIn_eq, bind, Id.run_pure]
  have key := loop_aux a
    (wrap (fun (_ : Unit) (st : Array Int × Nat × Nat × Nat) =>
      if st.2.2.1 < st.2.2.2 then
        if (st.1[st.2.2.1]! : Int) < 0 then
          pure (ForInStep.yield (st.1.swapIfInBounds st.2.1 st.2.2.1, st.2.1 + 1, st.2.2.1 + 1, st.2.2.2))
        else if (st.1[st.2.2.1]! : Int) = 0 then
          pure (ForInStep.yield (st.1, st.2.1, st.2.2.1 + 1, st.2.2.2))
        else
          pure (ForInStep.yield (st.1.swapIfInBounds st.2.2.1 (st.2.2.2 - 1), st.2.1, st.2.2.1, st.2.2.2 - 1))
      else pure (ForInStep.done (st.1, st.2.1, st.2.2.1, st.2.2.2))))
    (fun arr lo mid hi hg hx => wrap_yield (by simp only [if_pos hg, if_pos hx]))
    (fun arr lo mid hi hg hx1 hx2 => wrap_yield (by simp only [if_pos hg, if_neg hx1, if_pos hx2]))
    (fun arr lo mid hi hg hx1 hx2 => wrap_yield (by simp only [if_pos hg, if_neg hx1, if_neg hx2]))
    (fun arr lo mid hi hg => wrap_done (by simp only [if_neg hg]))
    a.size a 0 0 a.size (by omega)
    ⟨rfl, Array.Perm.refl a, Nat.le_refl 0, Nat.zero_le _, Nat.le_refl _,
      fun k hk => by omega, fun k hk1 hk2 => by omega, fun k hk1 hk2 => by omega⟩
  obtain ⟨⟨hsz, hperm, h1, h2, h3, hz1, hz2, hz3⟩, hmh⟩ := key
  exact ⟨hsz, hperm, _, _, h1, Nat.le_trans h2 h3, hz1, hz2,
    fun k hk1 hk2 => hz3 k (hmh ▸ hk1) hk2⟩

end Manual
