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

namespace Manual

/-! The same theorem without `vcgen`: an induction over the list with the seen-set and
the consumed prefix generalized, against the raw `forIn`.

Places to get stuck, each absent from the `vcgen` proof:

1. The aux statement carries the invariant (seen-set extensionally equals the prefix,
   prefix duplicate-free), both exit conditions, and the generalization over the
   prefix that relates them to the whole list, with the `forIn` term spelled once
   per conjunct.
2. The `seen := seen.insert x` mutation elaborates to `have` bindings inside the loop
   body, so the goal's lambda is not syntactically the plain lambda one would write:
   `rcases … :` on the hand-written form silently fails to substitute into the goal,
   and only replicating the `have` structure verbatim makes it match.
3. Mid-proof, `simp` normalizes those `have`s away again, so the case hypotheses
   produced by `rcases` stop matching the goal and must be transported across the
   definitional equality by re-stating them (`have hres' : … := hres`).
-/

set_option linter.unusedVariables false

private theorem loop_aux (l : List Int) : ∀ (seen : Std.HashSet Int) (pref : List Int),
    (∀ x, x ∈ seen ↔ x ∈ pref) → pref.Nodup →
    (∀ b, (forIn (m := Id) l ((none : Option Bool), seen) (fun x s =>
        if x ∈ s.2 then pure (.done (some true, s.2))
        else pure (.yield (none, s.2.insert x)))).run.1 = some b →
      b = true ∧ ¬(pref ++ l).Nodup) ∧
    ((forIn (m := Id) l ((none : Option Bool), seen) (fun x s =>
        if x ∈ s.2 then pure (.done (some true, s.2))
        else pure (.yield (none, s.2.insert x)))).run.1 = none →
      (pref ++ l).Nodup) := by
  induction l with
  | nil =>
    intro seen pref hseen hnodup
    refine ⟨fun b hb => ?_, fun _ => by simpa using hnodup⟩
    rw [List.forIn_nil] at hb
    injection hb
  | cons x xs ih =>
    intro seen pref hseen hnodup
    rw [List.forIn_cons]
    by_cases h : x ∈ seen
    · simp only [if_pos h, pure_bind]
      refine ⟨fun b hb => ?_, fun hnone => ?_⟩
      · injection hb with hb
        subst hb
        have : x ∈ pref := (hseen x).mp h
        grind
      · injection hnone
    · simp only [if_neg h, pure_bind]
      have hx : x ∉ pref := fun hx => h ((hseen x).mpr hx)
      obtain ⟨ih1, ih2⟩ := ih (seen.insert x) (pref ++ [x])
        (by grind) (by grind)
      refine ⟨fun b hb => ?_, fun hnone => ?_⟩
      · have := ih1 b hb
        grind
      · have := ih2 hnone
        grind

theorem hasDup_correct (l : List Int) :
    (hasDup l).run = true ↔ ¬ l.Nodup := by
  obtain ⟨h1, h2⟩ := loop_aux l ∅ [] (by simp) List.nodup_nil
  unfold hasDup
  rcases hres : (forIn (m := Id) l ((none : Option Bool), (∅ : Std.HashSet Int))
      (fun (x : Int) (__s : Option Bool × Std.HashSet Int) =>
        have seen := __s.snd
        if x ∈ seen then pure (.done (some true, seen))
        else
          have seen := seen.insert x
          pure (.yield (none, seen)))).run.1 with _ | b
  · have hnd : l.Nodup := by simpa using h2 hres
    have hres' : (forIn (m := Id) l ((none : Option Bool), (∅ : Std.HashSet Int))
        (fun (x : Int) (s : Option Bool × Std.HashSet Int) =>
          if x ∈ s.2 then pure (.done (some true, s.2))
          else pure (.yield (none, s.2.insert x)))).run.1 = none := hres
    simp [hres', hnd]
  · obtain ⟨rfl, hnd⟩ := h1 b hres
    have hnd' : ¬ l.Nodup := by simpa using hnd
    have hres' : (forIn (m := Id) l ((none : Option Bool), (∅ : Std.HashSet Int))
        (fun (x : Int) (s : Option Bool × Std.HashSet Int) =>
          if x ∈ s.2 then pure (.done (some true, s.2))
          else pure (.yield (none, s.2.insert x)))).run.1 = some true := hres
    simp [hres', hnd']

end Manual

/-! Sanity tests. -/
-- `native_decide`: `Std.HashSet` internals do not reduce in the kernel.
example : (hasDup [1, 2, 1]).run = true := by native_decide
example : (hasDup [1, 2, 3]).run = false := by native_decide
example : (hasDup []).run = false := by native_decide
example : (hasDup [7]).run = false := by native_decide
example : (hasDup [2, 2]).run = true := by native_decide
example : (hasDup [1, 2, 3, 4, 5, 3]).run = true := by native_decide
example : (hasDup [-1, 1]).run = false := by native_decide
