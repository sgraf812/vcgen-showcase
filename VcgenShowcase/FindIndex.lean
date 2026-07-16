import Std.Internal.Do
import Std.Tactic.Do

/-!
# Linear search with early return

`findIdx` returns the first index whose element equals the target. The spec pins down
first-ness: a hit at `i` means no hit before `i`, a miss means no hit anywhere.

The `vcgen` proof supplies one loop invariant. The early-return slot is `s.1`; the
`some` branch pins `xs.suffix = []` because the loop machinery asserts the invariant
at the full cursor once the loop has returned.

Two proofs of the same fact without `vcgen`:

* `Manual.findIdx_correct` reflects the loop into `List.find?` over `List.range'`
  (`findIdx_eq_find?`) and derives the spec from the `find?` API. The reflection is
  available because this loop coincides with a library combinator; its proof still
  goes through the desugaring bridge and one induction over the index list.
* `Manual.Raw.findIdx_correct` uses the same lemma base as the `vcgen` proof (the
  grind-annotated `List` and `Id` APIs) and no combinator theory: a
  start-offset-generalized induction over `List.range'` against the raw `forIn`.
  The aux statement is the loop invariant, the two exit conditions, and the
  impossible-state clause, written out three times over; each induction case is a
  `rw` for the list step, a `simp only` for the monad layer, and grind leaves with
  hand-picked induction-hypothesis instances.

Places to get stuck in the raw proof, each absent from the `vcgen` proof:

1. The aux statement itself: the invariant must be found *and* generalized over the
   start offset, extended with both exit conditions and the impossible-state clause,
   with the `forIn` expression spelled out once per conjunct.
2. Statement phrasing decides lemma coverage: the `Id` grind lemmas (`Id.run_pure`,
   `Id.run_bind`) are keyed on `.run`, so the aux must be phrased through `.run.1`
   for grind to reduce the monad layer, while the goal after `unfold` carries the
   bare `.fst`, so the final `rcases` must use the bare form and the aux applies
   only up to defeq.
3. The induction step must be hand-split: `induction ... with grind` diverges, with
   the induction hypothesis instantiated at derived arithmetic terms and the
   `range'` lemma set flooding the E-graph with equalities between unrelated
   ranges. `rw` the list step, `by_cases` the branch, instantiate the induction
   hypothesis explicitly, and only then grind.
4. `List.range'_succ` never fires by e-matching, since arithmetic normalization
   moves the `n + 1` out from under the pattern; the list step has to be a `rw`.
5. The desugaring bridge: the `Std.Legacy.Range.forIn_eq_forIn_range'` rewrite plus
   the arithmetic normalization of the range size, needed before the aux connects
   to the program at all.
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

/-- The loop is `List.find?` over the index list. -/
theorem findIdx_eq_find? (a : Array Int) (t : Int) :
    (findIdx a t).run = (List.range' 0 a.size).find? (fun i => a[i]! == t) := by
  unfold findIdx
  simp only [bind, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize List.range' 0 a.size = l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : a[x]! = t
    · rw [List.find?_cons_of_pos (by simpa using h)]
      simp only [List.forIn_cons, if_pos h, pure_bind]
      rfl
    · rw [List.find?_cons_of_neg (by simpa using h)]
      simpa [List.forIn_cons, h] using ih

theorem findIdx_correct (a : Array Int) (t : Int) :
    match (findIdx a t).run with
    | some i => i < a.size ∧ a[i]! = t ∧ ∀ j, j < i → a[j]! ≠ t
    | none => ∀ j, j < a.size → a[j]! ≠ t := by
  rw [findIdx_eq_find?]
  rcases h : (List.range' 0 a.size).find? (fun i => a[i]! == t) with _ | i
  · rw [List.find?_eq_none] at h
    intro j hj
    simpa using h j (by simp [List.mem_range'_1]; omega)
  · rw [List.find?_eq_some_iff_append] at h
    grind [List.range'_eq_append_iff]

namespace Raw

set_option linter.unusedVariables false

private theorem loop_aux (a : Array Int) (t : Int) (n s : Nat) :
    (∀ i, (forIn (m := Id) (List.range' s n) ((none : Option (Option Nat)), ())
        (fun i s => if a[i]! = t then pure (.done (some (some i), ())) else pure (.yield (none, ())))).run.1 = some (some i) →
      s ≤ i ∧ i < s + n ∧ a[i]! = t ∧ ∀ j, s ≤ j → j < i → a[j]! ≠ t) ∧
    ((forIn (m := Id) (List.range' s n) ((none : Option (Option Nat)), ())
        (fun i s => if a[i]! = t then pure (.done (some (some i), ())) else pure (.yield (none, ())))).run.1 = none →
      ∀ j, s ≤ j → j < s + n → a[j]! ≠ t) ∧
    (forIn (m := Id) (List.range' s n) ((none : Option (Option Nat)), ())
        (fun i s => if a[i]! = t then pure (.done (some (some i), ())) else pure (.yield (none, ())))).run.1 ≠ some none := by
  induction n generalizing s with
  | zero => grind
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    by_cases h : a[s]! = t
    · simp only [h, ite_true, pure_bind]
      refine ⟨fun i hi => ?_, fun hnone => ?_, fun hh => ?_⟩ <;> grind
    · simp only [h, ite_false, pure_bind]
      obtain ⟨ih1, ih2, ih3⟩ := ih (s + 1)
      refine ⟨fun i hi => ?_, fun hnone j hj1 hj2 => ?_, ih3⟩
      · have := ih1 i hi
        grind
      · have := ih2 hnone j
        grind

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

end Raw

end Manual

/-! Sanity tests. -/
example : (findIdx #[5, 3, 7, 3] 3).run = some 1 := by cbv
example : (findIdx #[5, 3, 7] 9).run = none := by cbv
example : (findIdx #[3, 3, 3] 3).run = some 0 := by cbv
example : (findIdx #[] 3).run = none := by cbv
example : (findIdx #[5, 3, 7] 7).run = some 2 := by cbv
