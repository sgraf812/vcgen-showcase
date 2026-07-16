import Std.Data.HashSet
import Std.Internal.Do
import Std.Tactic.Do

/-!
# Duplicate detection with a `HashSet`

`hasDup` walks the list with a seen-set and returns early on the first repeated
element. The spec relates the answer to `List.Nodup`.

The invariant tracks that the seen-set is exactly the consumed prefix and that the
prefix is duplicate-free. All verification conditions close by `finish` on the grind
API of `Std.HashSet` and `List.Nodup`.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

def hasDup (l : List Int) : Id Bool := do
  let mut seen : Std.HashSet Int := {}
  for x in l do
    if x ∈ seen then
      return true
    seen := seen.insert x
  return false

theorem hasDup_spec (l : List Int) :
    ⦃ True ⦄ hasDup l ⦃ fun r => r = true ↔ ¬ l.Nodup ⦄ := by
  vcgen [hasDup] invariants
  | inv1 => fun xs s => match s.1 with
    | none => (∀ x, x ∈ s.2 ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup
    | some true => xs.suffix = [] ∧ ¬ l.Nodup
    | some false => False
  with finish
