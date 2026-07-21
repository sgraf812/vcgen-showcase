import Std.Internal.Do
import Std.Tactic.Do

/-!
# Repro: a tactic `have`/`let` poisons the next `vcgen`

Toolchain: `leanprover/lean4:nightly-2026-07-15`.

Symptom: any tactic `have`, `let`, or `suffices` before a `vcgen` makes it fail with

    vcgen: could not determine the program type of the goal

on an otherwise ordinary `Triple` goal.

Cause: `have`/`let`/`suffices` desugar through `refine_lift no_implicit_lambda% …`, which
wraps the resulting goal type in a `noImplicitLambda` `mdata` node. `vcgen` reads the goal's
head to find the program type and does not see through that annotation, so it bails out. The
hypothesis type is irrelevant; a `have _h : True := trivial` is enough.

Run with: `lake env lean HaveTripleBug.lean`
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option linter.unusedVariables false

-- Without a preceding `have`, `vcgen` reads the program type and succeeds.
example : ⦃ fun _ => True ⦄ (pure 1 : StateM Nat Nat) ⦃ fun _ _ => True ⦄ := by
  vcgen

-- A `have` of an unrelated `True` is enough to poison the following `vcgen`.
/-- error: vcgen: could not determine the program type of the goal -/
#guard_msgs in
example : ⦃ fun _ => True ⦄ (pure 1 : StateM Nat Nat) ⦃ fun _ _ => True ⦄ := by
  have _h : True := trivial
  vcgen

-- `let` triggers it too.
/-- error: vcgen: could not determine the program type of the goal -/
#guard_msgs in
example : ⦃ fun _ => True ⦄ (pure 1 : StateM Nat Nat) ⦃ fun _ _ => True ⦄ := by
  let _n : Nat := 0
  vcgen
