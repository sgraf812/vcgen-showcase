import Std.Internal.Do
import Std.Tactic.Do

/-!
# First pair summing to a target, by nested loops

Brute-force search over all index pairs `i < j`, with the `return` exiting both loops.
The spec pins the result to a valid pair or certifies that none exists.

The `vcgen` proof supplies one invariant per loop; the inner one (`inv2`) has the
outer cursor and the outer invariant in scope. The inner invariant tracks the
already-scanned partners of the current `i` by membership in the inner prefix:
position arithmetic for the inner range (which starts at `i + 1`) is not derivable by
e-matching, while membership extends by exactly the split element at each step and
converts to bounds once, at the loop exit.

`Manual.findPair_correct` is the same-base baseline. Places to get stuck, beyond the
single-loop ones:

1. Two loops mean two aux lemmas, and the outer statement embeds the inner loop
   verbatim, so both programs are spelled in every conjunct.
2. The desugaring inserts a result-propagation `match` after the inner loop. Its
   auxiliary matcher can be neither replicated (a fresh matcher per declaration; the
   matcher cache misses) nor crossed by definitional equality at any transparency.
   The way through is to reference the elaborator's own matcher constant
   (`Break.runK.match_1`) in a combinator reimplementation (`findPair''`), after
   which the two programs agree by `simp` alone (`findPair_eq`).
3. Every case split on an intermediate loop result needs a `Prod.ext`-packaged
   equation pushed through the `Id` bind by a hand-written `show`/`rw` chain, once
   per loop level and branch.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

/-- First pair of indices (in lexicographic order) whose elements sum to `target`. -/
def findPair (a : Array Int) (target : Int) : Id (Option (Nat × Nat)) := do
  for i in [0:a.size] do
    for j in [i+1:a.size] do
      if a[i]! + a[j]! = target then
        return some (i, j)
  return none

theorem findPair_spec (a : Array Int) (t : Int) :
    ⦃ True ⦄ findPair a t
    ⦃ fun r => match r with
      | some (i, j) => i < j ∧ j < a.size ∧ a[i]! + a[j]! = t
      | none => ∀ i j, i < j → j < a.size → a[i]! + a[j]! ≠ t ⦄ := by
  vcgen [findPair] invariants
  | inv1 => fun xs s => match s.1 with
    | none => ∀ p q, p < xs.prefix.length → p < q → q < a.size → a[p]! + a[q]! ≠ t
    | some (some (i, j)) => xs.suffix = [] ∧ i < j ∧ j < a.size ∧ a[i]! + a[j]! = t
    | some none => False
  | inv2 pref cur suff hsplit b hinv => fun ys s => match s.1 with
    | none =>
        (∀ p q, p < cur → p < q → q < a.size → a[p]! + a[q]! ≠ t) ∧
        (∀ q, q ∈ ys.prefix → a[cur]! + a[q]! ≠ t)
    | some (some (i, j)) => ys.suffix = [] ∧ i < j ∧ j < a.size ∧ a[i]! + a[j]! = t
    | some none => False
  with finish

namespace Manual

set_option linter.unusedVariables false

/-- The inner-loop result propagation step of the desugared `findPair`, spelled with the
same auxiliary matcher (`Break.runK.match_1`) that the `do` elaborator used. -/
def propagate (x : Option (Option (Nat × Nat)) × Unit) :
    Id (ForInStep (Option (Option (Nat × Nat)) × Unit)) :=
  Break.runK.match_1 (fun _ => Id (ForInStep (Option (Option (Nat × Nat)) × Unit))) x.1
    (fun r => pure (.done (some r, ()))) (fun _ => pure (.yield (none, ())))

def postlude (x : Option (Option (Nat × Nat)) × Unit) : Id (Option (Nat × Nat)) :=
  Break.runK.match_1 (fun _ => Id (Option (Nat × Nat))) x.1
    (fun r => pure r) (fun _ => pure none)

def findPair'' (a : Array Int) (t : Int) : Id (Option (Nat × Nat)) :=
  (forIn (m := Id) (List.range' 0 a.size) ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun i _ =>
    (forIn (m := Id) (List.range' (i+1) (a.size - (i+1))) ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
      if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
      else pure (.yield (none, ())))) >>= propagate)) >>= postlude

theorem findPair_eq (a : Array Int) (t : Int) : findPair a t = findPair'' a t := by
  unfold findPair findPair'' propagate postlude
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]

theorem propagate_some (r : Option (Nat × Nat)) :
    propagate (some r, ()) = pure (ForInStep.done (some r, ())) := rfl
theorem propagate_none : propagate (none, ()) = pure (ForInStep.yield (none, ())) := rfl
theorem postlude_some (r : Option (Nat × Nat)) : postlude (some r, ()) = pure r := rfl
theorem postlude_none : postlude (none, ()) = pure none := rfl

set_option linter.unusedVariables false

private theorem inner_aux (a : Array Int) (t : Int) (i : Nat) (l : List Nat) :
    (∀ r, (forIn (m := Id) l ((none, ()) : Option (Option (Nat × Nat)) × Unit)
        (fun j _ => if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
          else pure (.yield (none, ())))).1 = some r →
      ∃ j ∈ l, r = some (i, j) ∧ a[i]! + a[j]! = t) ∧
    ((forIn (m := Id) l ((none, ()) : Option (Option (Nat × Nat)) × Unit)
        (fun j _ => if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
          else pure (.yield (none, ())))).1 = none →
      ∀ j ∈ l, a[i]! + a[j]! ≠ t) := by
  induction l with
  | nil =>
    refine ⟨fun r hr => ?_, fun _ j hj => absurd hj (List.not_mem_nil)⟩
    rw [List.forIn_nil] at hr
    injection hr
  | cons x xs ih =>
    rw [List.forIn_cons]
    by_cases h : a[i]! + a[x]! = t
    · simp only [if_pos h, pure_bind]
      refine ⟨fun r hr => ?_, fun hnone => ?_⟩
      · injection hr with hr
        exact ⟨x, List.mem_cons_self, by grind⟩
      · injection hnone
    · simp only [if_neg h, pure_bind]
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨fun r hr => ?_, fun hnone j hj => ?_⟩
      · obtain ⟨j, hj, hr⟩ := ih1 r hr
        exact ⟨j, List.mem_cons_of_mem x hj, hr⟩
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact h
        · exact ih2 hnone j hj

private theorem outer_aux (a : Array Int) (t : Int) : ∀ l : List Nat,
    (∀ r, (forIn (m := Id) l ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun i _ =>
        (forIn (m := Id) (List.range' (i+1) (a.size - (i+1))) ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
          if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
          else pure (.yield (none, ())))) >>= propagate)).1 = some r →
      ∃ i j, i < j ∧ j < a.size ∧ r = some (i, j) ∧ a[i]! + a[j]! = t) ∧
    ((forIn (m := Id) l ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun i _ =>
        (forIn (m := Id) (List.range' (i+1) (a.size - (i+1))) ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
          if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
          else pure (.yield (none, ())))) >>= propagate)).1 = none →
      ∀ i ∈ l, ∀ j, i < j → j < a.size → a[i]! + a[j]! ≠ t) := by
  intro l
  induction l with
  | nil =>
    refine ⟨fun r hr => ?_, fun _ i hi => absurd hi (List.not_mem_nil)⟩
    rw [List.forIn_nil] at hr
    injection hr
  | cons x xs ih =>
    rw [List.forIn_cons]
    obtain ⟨in1, in2⟩ := inner_aux a t x (List.range' (x+1) (a.size - (x+1)))
    rcases hres : (forIn (m := Id) (List.range' (x+1) (a.size - (x+1)))
        ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
          if a[x]! + a[j]! = t then pure (.done (some (some (x, j)), ()))
          else pure (.yield (none, ())))).1 with _ | r
    · have hstep : (forIn (m := Id) (List.range' (x+1) (a.size - (x+1)))
          ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
            if a[x]! + a[j]! = t then pure (.done (some (some (x, j)), ()))
            else pure (.yield (none, ())))) >>= propagate = pure (ForInStep.yield (none, ())) := by
        show propagate _ = _
        rw [show (forIn (m := Id) (List.range' (x+1) (a.size - (x+1)))
          ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
            if a[x]! + a[j]! = t then pure (.done (some (some (x, j)), ()))
            else pure (.yield (none, ())))) = ((none : Option (Option (Nat × Nat))), ()) from
          Prod.ext hres rfl]
        exact propagate_none
      rw [hstep, pure_bind]
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨ih1, fun hnone i hi j hij hj => ?_⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact in2 hres j (List.mem_range'_1.mpr ⟨hij, by omega⟩)
      · exact ih2 hnone i hi j hij hj
    · have hstep : (forIn (m := Id) (List.range' (x+1) (a.size - (x+1)))
          ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
            if a[x]! + a[j]! = t then pure (.done (some (some (x, j)), ()))
            else pure (.yield (none, ())))) >>= propagate = pure (ForInStep.done (some r, ())) := by
        show propagate _ = _
        rw [show (forIn (m := Id) (List.range' (x+1) (a.size - (x+1)))
          ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
            if a[x]! + a[j]! = t then pure (.done (some (some (x, j)), ()))
            else pure (.yield (none, ())))) = (some r, ()) from Prod.ext hres rfl]
        exact propagate_some r
      rw [hstep, pure_bind]
      obtain ⟨j, hj, rfl, hhit⟩ := in1 r hres
      have hjb := List.mem_range'_1.mp hj
      refine ⟨fun r' hr' => ?_, fun hnone => ?_⟩
      · injection hr' with hr'
        exact ⟨x, j, by omega, by omega, hr'.symm, hhit⟩
      · injection hnone

theorem findPair_correct (a : Array Int) (t : Int) :
    match (findPair a t).run with
    | some (i, j) => i < j ∧ j < a.size ∧ a[i]! + a[j]! = t
    | none => ∀ i j, i < j → j < a.size → a[i]! + a[j]! ≠ t := by
  rw [findPair_eq]
  unfold findPair''
  obtain ⟨h1, h2⟩ := outer_aux a t (List.range' 0 a.size)
  rcases hres : (forIn (m := Id) (List.range' 0 a.size)
      ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun i _ =>
        (forIn (m := Id) (List.range' (i+1) (a.size - (i+1))) ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
          if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
          else pure (.yield (none, ())))) >>= propagate)).1 with _ | r
  · rw [show ((forIn (m := Id) (List.range' 0 a.size)
        ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun i _ =>
          (forIn (m := Id) (List.range' (i+1) (a.size - (i+1))) ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
            if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
            else pure (.yield (none, ())))) >>= propagate)) >>= postlude : Id (Option (Nat × Nat)))
      = postlude ((none : Option (Option (Nat × Nat))), ()) from by
        show postlude _ = _
        rw [show (forIn (m := Id) (List.range' 0 a.size)
          ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun i _ =>
            (forIn (m := Id) (List.range' (i+1) (a.size - (i+1))) ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
              if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
              else pure (.yield (none, ())))) >>= propagate)) = ((none : Option (Option (Nat × Nat))), ()) from
          Prod.ext hres rfl],
      postlude_none]
    intro i j hij hj
    exact h2 hres i (List.mem_range'_1.mpr ⟨Nat.zero_le i, by omega⟩) j hij hj
  · rw [show ((forIn (m := Id) (List.range' 0 a.size)
        ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun i _ =>
          (forIn (m := Id) (List.range' (i+1) (a.size - (i+1))) ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
            if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
            else pure (.yield (none, ())))) >>= propagate)) >>= postlude : Id (Option (Nat × Nat)))
      = postlude (some r, ()) from by
        show postlude _ = _
        rw [show (forIn (m := Id) (List.range' 0 a.size)
          ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun i _ =>
            (forIn (m := Id) (List.range' (i+1) (a.size - (i+1))) ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
              if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
              else pure (.yield (none, ())))) >>= propagate)) = (some r, ()) from
          Prod.ext hres rfl],
      postlude_some]
    obtain ⟨i, j, hij, hj, rfl, hhit⟩ := h1 r hres
    exact ⟨hij, hj, hhit⟩

end Manual
