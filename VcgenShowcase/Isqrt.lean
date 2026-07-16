import Std.Internal.Do
import Std.Tactic.Do

/-!
# Integer square root by linear search

A `while` loop in `Id`. The proof supplies the loop invariant (`inv1`, split into the
looping state `.inl` and the exit state `.inr`) and the termination variant (`inv2`).
`finish` discharges the verification conditions, including the nonlinear arithmetic.

`while` loops elaborate to a `partial_fixpoint`; there is no unfolding-based proof to
contrast with, since any direct proof has to invent fixpoint induction first.
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
