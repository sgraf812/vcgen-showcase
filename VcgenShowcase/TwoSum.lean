import Std.Internal.Do
import Std.Tactic.Do
import Init.Internal.Order.While
import VcgenShowcase.ManualLoop

/-!
# Two-sum on a sorted array

The two-pointer search: move `lo` up when the sum is too small, `hi` down when it is
too large, return the pair when it matches. The correctness argument is the exclusion
invariant: every index pair summing to the target lies inside the current window,
maintained using sortedness. The variant is `hi - lo`.

The `vcgen` proof supplies that invariant against the `.inl`/`.inr` split of the
`while` state, whose looping component carries the early-return slot
(`Option (Option (Nat × Nat)) × Nat × Nat`), and `finish` discharges everything,
including the sortedness instantiations.

`Manual.twoSum_correct` is the same-base baseline. Places to get stuck, beyond those
in `Isqrt.Manual` (fuel, sanctioned unfolding, `Id` projection phrasing):

1. Matcher identity is fatal to inline replication here: the `ForInStep` wrapper
   `match` that `Lean.Loop.forIn` builds around the body elaborates to a fresh
   auxiliary matcher in every declaration that spells it, so `rcases`/`rw` against a
   hand-written copy silently fail. The way out is a named combinator (`wrap`) plus
   the equation `loop_forIn_eq`, provable only by `with_unfolding_all rfl`
   (kernel-transparency definitional equality is the one tool that crosses matcher
   identity).
2. Type abbreviations poison syntactic matching: a state tuple spelled with an
   abbreviation fails to generalize against the goal, which carries the unfolded
   product type.
3. The window invariant, the fuel bound, and all three exit conditions (hit, exhaust,
   early return) must be threaded through a five-way case split per unfolding step;
   the `vcgen` proof states the invariant once and gets the splits from the loop
   rule.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

def twoSum (a : Array Int) (target : Int) : Id (Option (Nat × Nat)) := do
  let mut lo := 0
  let mut hi := a.size - 1
  while lo < hi do
    let s := a[lo]! + a[hi]!
    if s = target then
      return some (lo, hi)
    else if s < target then
      lo := lo + 1
    else
      hi := hi - 1
  return none

@[grind] def Sorted (a : Array Int) : Prop :=
  ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!

theorem twoSum_spec (a : Array Int) (t : Int) (hs : Sorted a) :
    ⦃ True ⦄ twoSum a t
    ⦃ fun r => match r with
      | some (i, j) => i < j ∧ j < a.size ∧ a[i]! + a[j]! = t
      | none => ∀ i j, i < j → j < a.size → a[i]! + a[j]! ≠ t ⦄ := by
  vcgen [twoSum] invariants
  | inv1 => fun s => match s with
    | .inl (ret, lo, hi) => ret = none ∧ hi ≤ a.size - 1 ∧
        (∀ i j, i < j → j < a.size → a[i]! + a[j]! = t → lo ≤ i ∧ j ≤ hi)
    | .inr (ret, lo, hi) => match ret with
      | some (some (i, j)) => i < j ∧ j < a.size ∧ a[i]! + a[j]! = t
      | some none => False
      | none => ∀ i j, i < j → j < a.size → a[i]! + a[j]! ≠ t
  | inv2 => fun s => s.2.2 - s.2.1
  with finish

namespace Manual

set_option linter.unusedVariables false

private theorem loop_aux (a : Array Int) (t : Int)
    (hs : ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!)
    (F : (Option (Option (Nat × Nat)) × Nat × Nat) → Id ((Option (Option (Nat × Nat)) × Nat × Nat) ⊕ (Option (Option (Nat × Nat)) × Nat × Nat)))
    (hhit : ∀ r lo hi, lo < hi → a[lo]! + a[hi]! = t →
      F (r, lo, hi) = pure (Sum.inr (some (some (lo, hi)), lo, hi)))
    (hlt : ∀ r lo hi, lo < hi → a[lo]! + a[hi]! ≠ t → a[lo]! + a[hi]! < t →
      F (r, lo, hi) = pure (Sum.inl (none, lo + 1, hi)))
    (hgt : ∀ r lo hi, lo < hi → a[lo]! + a[hi]! ≠ t → ¬ a[lo]! + a[hi]! < t →
      F (r, lo, hi) = pure (Sum.inl (none, lo, hi - 1)))
    (hstop : ∀ r lo hi, ¬ lo < hi → F (r, lo, hi) = pure (Sum.inr (none, lo, hi))) :
    ∀ fuel r lo hi, hi - lo ≤ fuel → hi ≤ a.size - 1 →
      (∀ i j, i < j → j < a.size → a[i]! + a[j]! = t → lo ≤ i ∧ j ≤ hi) →
      match (repeatM (m := Id) F (r, lo, hi)).1 with
      | some (some (i, j)) => i < j ∧ j < a.size ∧ a[i]! + a[j]! = t
      | some none => False
      | none => ∀ i j, i < j → j < a.size → a[i]! + a[j]! ≠ t := by
  intro fuel
  induction fuel with
  | zero =>
    intro r lo hi hfuel hbound hconf
    rw [repeatM_eq_of_monadTail]
    have hguard : ¬ lo < hi := by omega
    simp only [repeatM.body, hstop r lo hi hguard, pure_bind]
    intro i j hij hj hsum
    have := hconf i j hij hj hsum
    omega
  | succ fuel ih =>
    intro r lo hi hfuel hbound hconf
    rw [repeatM_eq_of_monadTail]
    by_cases hguard : lo < hi
    · by_cases hsum : a[lo]! + a[hi]! = t
      · simp only [repeatM.body, hhit r lo hi hguard hsum, pure_bind]
        exact ⟨hguard, by omega, hsum⟩
      · by_cases hless : a[lo]! + a[hi]! < t
        · simp only [repeatM.body, hlt r lo hi hguard hsum hless, pure_bind]
          refine ih none (lo + 1) hi (by omega) hbound ?_
          intro i j hij hj hsc
          obtain ⟨h1, h2⟩ := hconf i j hij hj hsc
          refine ⟨?_, h2⟩
          rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
          · exfalso
            have hj' : a[j]! ≤ a[hi]! := hs j hi h2 (by omega)
            omega
          · omega
        · simp only [repeatM.body, hgt r lo hi hguard hsum hless, pure_bind]
          refine ih none lo (hi - 1) (by omega) (by omega) ?_
          intro i j hij hj hsc
          obtain ⟨h1, h2⟩ := hconf i j hij hj hsc
          refine ⟨h1, ?_⟩
          rcases Nat.eq_or_lt_of_le h2 with rfl | h2'
          · exfalso
            have hi' : a[lo]! ≤ a[i]! := hs lo i h1 (by omega)
            omega
          · omega
    · simp only [repeatM.body, hstop r lo hi hguard, pure_bind]
      intro i j hij hj hsum
      have := hconf i j hij hj hsum
      omega

theorem twoSum_correct (a : Array Int) (t : Int)
    (hs : ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!) :
    match (twoSum a t).run with
    | some (i, j) => i < j ∧ j < a.size ∧ a[i]! + a[j]! = t
    | none => ∀ i j, i < j → j < a.size → a[i]! + a[j]! ≠ t := by
  unfold twoSum
  simp only [loop_forIn_eq, bind]
  have key := loop_aux a t hs
    (wrap (fun (_ : Unit) (b : Option (Option (Nat × Nat)) × Nat × Nat) =>
      if b.2.1 < b.2.2 then
        if a[b.2.1]! + a[b.2.2]! = t then
          pure (ForInStep.done (some (some (b.2.1, b.2.2)), b.2.1, b.2.2))
        else if a[b.2.1]! + a[b.2.2]! < t then
          pure (ForInStep.yield (none, b.2.1 + 1, b.2.2))
        else pure (ForInStep.yield (none, b.2.1, b.2.2 - 1))
      else pure (ForInStep.done (none, b.2.1, b.2.2))))
    (fun r lo hi hg hsum => wrap_done (by simp only [if_pos hg, if_pos hsum]))
    (fun r lo hi hg hne hlt => wrap_yield (by simp only [if_pos hg, if_neg hne, if_pos hlt]))
    (fun r lo hi hg hne hge => wrap_yield (by simp only [if_pos hg, if_neg hne, if_neg hge]))
    (fun r lo hi hg => wrap_done (by simp only [if_neg hg]))
    a.size none 0 (a.size - 1) (by omega) (by omega)
    (fun i j hij hj _ => ⟨Nat.zero_le i, by omega⟩)
  rcases hres : (repeatM (m := Id) (wrap (fun (_ : Unit) (b : Option (Option (Nat × Nat)) × Nat × Nat) =>
      if b.2.1 < b.2.2 then
        if a[b.2.1]! + a[b.2.2]! = t then
          pure (ForInStep.done (some (some (b.2.1, b.2.2)), b.2.1, b.2.2))
        else if a[b.2.1]! + a[b.2.2]! < t then
          pure (ForInStep.yield (none, b.2.1 + 1, b.2.2))
        else pure (ForInStep.yield (none, b.2.1, b.2.2 - 1))
      else pure (ForInStep.done (none, b.2.1, b.2.2))))
      ((none, 0, a.size - 1) : Option (Option (Nat × Nat)) × Nat × Nat)).1 with _ | (_ | ⟨i, j⟩) <;>
    · rw [hres] at key
      first
        | exact key
        | exact key.elim
        | exact fun i j hij hj => key i j hij hj

end Manual

/-! Sanity tests. -/
-- `native_decide`: the program does not reduce in the kernel (`repeatM.impl` is opaque).
example : (twoSum #[1, 2, 3, 4] 7).run = some (2, 3) := by native_decide
example : (twoSum #[1, 2, 3, 4] 42).run = none := by native_decide
