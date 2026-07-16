import Std.Internal.Do
import Std.Tactic.Do
import Init.Internal.Order.While

/-!
# Integer square root by linear search

A `while` loop in `Id`. The proof supplies the loop invariant (`inv1`, split into the
looping state `.inl` and the exit state `.inr`) and the termination variant (`inv2`).
`finish` discharges the verification conditions, including the nonlinear arithmetic.

`while` loops elaborate to the `repeatM` least fixpoint. `Manual.isqrt_correct` proves
the same theorem by unfolding that fixpoint step by step under an explicit fuel
induction.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

def isqrt (n : Nat) : Id Nat := do
  let mut r := 0
  while (r + 1) * (r + 1) ≤ n do
    r := r + 1
  return r

theorem isqrt_spec (n : Nat) :
    ⦃ True ⦄ isqrt n ⦃ fun r => r * r ≤ n ∧ n < (r + 1) * (r + 1) ⦄ := by
  vcgen [isqrt] invariants
  | inv1 => fun r => match r with
    | .inl r => r * r ≤ n
    | .inr r => r * r ≤ n ∧ n < (r + 1) * (r + 1)
  | inv2 => fun r => n - r
  with finish

namespace Manual

/-! The same theorem without `vcgen`, against the `repeatM` fixpoint that `while`
elaborates to (via `Lean.Loop.forIn`). The loop body is abstracted as `F` together
with its two reduction equations, and the induction is on explicit fuel `n - r`,
unfolding the fixpoint once per step with `repeatM_eq_of_monadTail`.

Places to get stuck, each absent from the `vcgen` proof:

1. Finding the unfolding lemma at all: `repeatM` is opaque; its one sanctioned
   unfolding `repeatM_eq_of_monadTail` lives in `Init.Internal.Order.While` behind a
   `MonadTail` instance, and nothing in the goal points there.
2. The variant must become explicit fuel, with the invariant `r * r ≤ n` and the
   fuel bound `n - r ≤ fuel` threaded through every case; `vcgen` takes the variant
   as the `inv2` clause and hides the induction.
3. Matcher identity: the aux lemma cannot be stated against a hand-written copy of
   the loop body, because the copy elaborates its `match` to a different auxiliary
   matcher than the one inside `isqrt`; `rw`, `show` and even `exact`-unification
   fail across the two. Abstracting the body as `F` with equation hypotheses and
   discharging them at the use site (where `rfl` sees the right matcher) is the way
   out.
4. `match (pure x : Id _) with …` does not iota-reduce syntactically and the entire
   `Id` simp set is keyed on `.run`, so the body equations must produce `pure`-free
   right-hand sides before any reduction happens.
-/

set_option linter.unusedVariables false

private theorem loop_aux (n fuel : Nat) (F : Nat → Id (Nat ⊕ Nat))
    (hyield : ∀ b, (b + 1) * (b + 1) ≤ n → F b = pure (Sum.inl (b + 1)))
    (hdone : ∀ b, ¬(b + 1) * (b + 1) ≤ n → F b = pure (Sum.inr b)) :
    ∀ r, n - r ≤ fuel → r * r ≤ n →
      (repeatM (m := Id) F r).run * (repeatM (m := Id) F r).run ≤ n ∧
        n < ((repeatM (m := Id) F r).run + 1) * ((repeatM (m := Id) F r).run + 1) := by
  induction fuel with
  | zero =>
    intro r hfuel hr
    rw [repeatM_eq_of_monadTail]
    have hstop : ¬(r + 1) * (r + 1) ≤ n := by grind
    simp only [repeatM.body, hdone r hstop, pure_bind, Id.run_pure]
    grind
  | succ fuel ih =>
    intro r hfuel hr
    rw [repeatM_eq_of_monadTail]
    by_cases h : (r + 1) * (r + 1) ≤ n
    · simp only [repeatM.body, hyield r h, pure_bind]
      exact ih (r + 1) (by grind) (by grind)
    · simp only [repeatM.body, hdone r h, pure_bind, Id.run_pure]
      grind

theorem isqrt_correct (n : Nat) :
    (isqrt n).run * (isqrt n).run ≤ n ∧
      n < ((isqrt n).run + 1) * ((isqrt n).run + 1) := by
  unfold isqrt
  simp only [forIn, Lean.Loop.forIn, bind, Id.run_pure]
  refine loop_aux n n _ (fun b hb => ?_) (fun b hb => ?_) 0 (by omega) (by simp)
  · simp only [if_pos hb]; rfl
  · simp only [if_neg hb]; rfl

end Manual

/-! Sanity tests. -/
-- `native_decide`: the program does not reduce in the kernel (`repeatM.impl` is opaque).
example : (isqrt 10).run = 3 := by native_decide
example : (isqrt 16).run = 4 := by native_decide
