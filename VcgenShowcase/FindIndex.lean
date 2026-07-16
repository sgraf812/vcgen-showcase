import Std.Internal.Do
import Std.Tactic.Do

/-!
# Linear search with early return

`findIdx` returns the first index whose element equals the target. The spec pins down
first-ness: a hit at `i` means no hit before `i`, a miss means no hit anywhere.

The `vcgen` proof supplies one loop invariant. The early-return slot is `s.1`; the
`some` branch pins `xs.suffix = []` because the loop machinery asserts the invariant
at the full cursor once the loop has returned.

`Manual.findIdx_correct` proves the same fact against the raw `forIn` desugaring:
a start-offset-generalized induction over `List.range'` threading the `ForInStep`
state machine.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

def findIdx (a : Array Int) (target : Int) : Id (Option Nat) := do
  for i in [0:a.size] do
    if a[i]! = target then
      return some i
  return none

theorem findIdx_spec (a : Array Int) (t : Int) :
    ⦃ True ⦄ findIdx a t
    ⦃ fun r => match r with
      | some i => i < a.size ∧ a[i]! = t ∧ ∀ j, j < i → a[j]! ≠ t
      | none => ∀ j, j < a.size → a[j]! ≠ t ⦄ := by
  vcgen [findIdx] invariants
  | inv1 => fun xs s => match s.1 with
    | none => ∀ j, j < xs.prefix.length → a[j]! ≠ t
    | some (some i) => xs.suffix = [] ∧ i < a.size ∧ a[i]! = t ∧ ∀ j, j < i → a[j]! ≠ t
    | some none => False
  with finish

namespace Manual

/-! The same theorem without `vcgen`, against the raw desugaring

```
do let __s ← forIn [:a.size] (none, ()) fun i __s =>
       if a[i]! = target then pure (.done (some (some i), ())) else pure (.yield (none, ()))
   match __s.fst with
   | some r => pure r
   | none => pure none
```

The loop lemma must be stated for an arbitrary start offset `s` so that the
induction goes through, and against the literal body lambda so that it applies
to the goal. -/

set_option linter.unusedVariables false

private theorem loop_aux (a : Array Int) (t : Int) (n s : Nat) :
    (∀ i, (forIn (m := Id) (List.range' s n) ((none : Option (Option Nat)), ())
        (fun i s => if a[i]! = t then pure (.done (some (some i), ())) else pure (.yield (none, ())))).1 = some (some i) →
      s ≤ i ∧ i < s + n ∧ a[i]! = t ∧ ∀ j, s ≤ j → j < i → a[j]! ≠ t) ∧
    ((forIn (m := Id) (List.range' s n) ((none : Option (Option Nat)), ())
        (fun i s => if a[i]! = t then pure (.done (some (some i), ())) else pure (.yield (none, ())))).1 = none →
      ∀ j, s ≤ j → j < s + n → a[j]! ≠ t) ∧
    (forIn (m := Id) (List.range' s n) ((none : Option (Option Nat)), ())
        (fun i s => if a[i]! = t then pure (.done (some (some i), ())) else pure (.yield (none, ())))).1 ≠ some none := by
  induction n generalizing s with
  | zero =>
    refine ⟨fun i h => by simp [List.forIn_nil] at h, fun _ j h1 h2 => by omega, by simp [List.forIn_nil]⟩
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    by_cases h : a[s]! = t
    · simp only [if_pos h, pure_bind]
      refine ⟨fun i hi => ?_, fun hnone => ?_, fun hh => ?_⟩
      · injection hi with hi
        injection hi with hi
        subst hi
        exact ⟨Nat.le_refl s, by omega, h, fun j h1 h2 => by omega⟩
      · injection hnone
      · injection hh with hh
        injection hh
    · simp only [if_neg h, pure_bind]
      obtain ⟨ih1, ih2, ih3⟩ := ih (s + 1)
      refine ⟨fun i hi => ?_, fun hnone j hj1 hj2 => ?_, ih3⟩
      · obtain ⟨h1, h2, h3, h4⟩ := ih1 i hi
        refine ⟨by omega, by omega, h3, fun j hj1 hj2 => ?_⟩
        by_cases hjs : j = s
        · subst hjs; exact h
        · exact h4 j (by omega) hj2
      · by_cases hjs : j = s
        · subst hjs; exact h
        · exact ih2 hnone j (by omega) (by omega)

theorem findIdx_correct (a : Array Int) (t : Int) :
    match (findIdx a t).run with
    | some i => i < a.size ∧ a[i]! = t ∧ ∀ j, j < i → a[j]! ≠ t
    | none => ∀ j, j < a.size → a[j]! ≠ t := by
  obtain ⟨h1, h2, h3⟩ := loop_aux a t a.size 0
  unfold findIdx
  simp only [bind, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Nat.zero_add] at *
  rcases hres : (forIn (m := Id) (List.range' 0 a.size) ((none : Option (Option Nat)), ())
      (fun i s => if a[i]! = t then pure (.done (some (some i), ())) else pure (.yield (none, ())))).1
    with _ | (_ | i)
  · exact fun j hj => h2 hres j (Nat.zero_le j) hj
  · exact absurd hres h3
  · obtain ⟨_, hlt, hhit, hmin⟩ := h1 i hres
    exact ⟨hlt, hhit, fun j hj => hmin j (Nat.zero_le j) hj⟩

end Manual
