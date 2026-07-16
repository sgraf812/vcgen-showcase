import Std.Internal.Do
import Std.Tactic.Do
import VcgenShowcase.RangeSplit

/-!
# First pair summing to a target, by nested loops

Brute-force search over all index pairs `i < j`, with the `return` exiting both
loops. The spec pins the result completely: the returned pair is valid and
lexicographically least among all valid pairs, and `none` certifies that no valid
pair exists.

The `vcgen` proof supplies one invariant per loop; the inner one (`inv2`) has the
outer cursor and the outer invariant in scope. First-ness needs the loop positions:
two seeded rules over the cursor split `List.range' s n = pref ++ c :: suff` give
the split element's position (`range'_split_pos`) and the prefix as an interval
(`range'_split_mem_prefix`); both trigger on the split, so `finish` converts between
"scanned so far" and index bounds in either direction.

`Manual.findPair_correct` is the same-base baseline for the same statement. Places
to get stuck, beyond the single-loop ones:

1. Two loops mean two aux lemmas, and the outer statement embeds the inner loop
   verbatim, so both programs are spelled in every conjunct. First-ness makes the
   split positions part of the statements: each aux returns the consumed prefix as
   a list split, and the main theorem converts splits to index bounds by hand with
   the same two `range'` rules.
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

/-- The first pair of indices, in lexicographic order, whose elements sum to `target`. -/
def findPair (a : Array Int) (target : Int) : Id (Option (Nat × Nat)) := do
  for i in [0:a.size] do
    for j in [i+1:a.size] do
      if a[i]! + a[j]! = target then
        return some (i, j)
  return none

theorem findPair_spec (a : Array Int) (t : Int) :
    ⦃ True ⦄ findPair a t
    ⦃ fun r => match r with
      | some (i, j) => i < j ∧ j < a.size ∧ a[i]! + a[j]! = t ∧
          ∀ p q, p < q → q < a.size → a[p]! + a[q]! = t → i < p ∨ (i = p ∧ j ≤ q)
      | none => ∀ i j, i < j → j < a.size → a[i]! + a[j]! ≠ t ⦄ := by
  vcgen [findPair] invariants
  | inv1 => fun xs s => match s.1 with
    | none => ∀ p q, p < xs.prefix.length → p < q → q < a.size → a[p]! + a[q]! ≠ t
    | some (some (i, j)) => xs.suffix = [] ∧ i < j ∧ j < a.size ∧ a[i]! + a[j]! = t ∧
        ∀ p q, p < q → q < a.size → a[p]! + a[q]! = t → i < p ∨ (i = p ∧ j ≤ q)
    | some none => False
  | inv2 pref cur suff hsplit b hinv => fun ys s => match s.1 with
    | none =>
        (∀ p q, p < cur → p < q → q < a.size → a[p]! + a[q]! ≠ t) ∧
        (∀ q, q ∈ ys.prefix → a[cur]! + a[q]! ≠ t)
    | some (some (i, j)) => ys.suffix = [] ∧ i < j ∧ j < a.size ∧ a[i]! + a[j]! = t ∧
        ∀ p q, p < q → q < a.size → a[p]! + a[q]! = t → i < p ∨ (i = p ∧ j ≤ q)
    | some none => False
  with finish

namespace Manual

set_option linter.unusedVariables false

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

private theorem inner_aux (a : Array Int) (t : Int) (i : Nat) (l : List Nat) :
    (∀ r, (forIn (m := Id) l ((none, ()) : Option (Option (Nat × Nat)) × Unit)
        (fun j _ => if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
          else pure (.yield (none, ())))).1 = some r →
      ∃ pre j post, l = pre ++ j :: post ∧ r = some (i, j) ∧ a[i]! + a[j]! = t ∧
        ∀ q ∈ pre, a[i]! + a[q]! ≠ t) ∧
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
        exact ⟨[], x, xs, rfl, by grind, h, fun q hq => absurd hq (List.not_mem_nil)⟩
      · injection hnone
    · simp only [if_neg h, pure_bind]
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨fun r hr => ?_, fun hnone j hj => ?_⟩
      · obtain ⟨pre, j, post, rfl, hr, hhit, hmin⟩ := ih1 r hr
        refine ⟨x :: pre, j, post, rfl, hr, hhit, fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact h
        · exact hmin q hq
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact h
        · exact ih2 hnone j hj

private theorem outer_aux (a : Array Int) (t : Int) : ∀ l : List Nat,
    (∀ r, (forIn (m := Id) l ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun i _ =>
        (forIn (m := Id) (List.range' (i+1) (a.size - (i+1))) ((none, ()) : Option (Option (Nat × Nat)) × Unit) (fun j _ =>
          if a[i]! + a[j]! = t then pure (.done (some (some (i, j)), ()))
          else pure (.yield (none, ())))) >>= propagate)).1 = some r →
      ∃ preI i postI, l = preI ++ i :: postI ∧
        (∀ p ∈ preI, ∀ q, p < q → q < a.size → a[p]! + a[q]! ≠ t) ∧
        ∃ pre j post, List.range' (i+1) (a.size - (i+1)) = pre ++ j :: post ∧
          r = some (i, j) ∧ a[i]! + a[j]! = t ∧ ∀ q ∈ pre, a[i]! + a[q]! ≠ t) ∧
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
      have hxcov : ∀ q, x < q → q < a.size → a[x]! + a[q]! ≠ t := fun q hq1 hq2 =>
        in2 hres q (List.mem_range'_1.mpr ⟨hq1, by omega⟩)
      refine ⟨fun r hr => ?_, fun hnone i hi j hij hj => ?_⟩
      · obtain ⟨preI, i, postI, rfl, houter, hinner⟩ := ih1 r hr
        refine ⟨x :: preI, i, postI, rfl, fun p hp => ?_, hinner⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hxcov
        · exact houter p hp
      · rcases List.mem_cons.mp hi with rfl | hi
        · exact hxcov j hij hj
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
      obtain ⟨pre, j, post, hsplit, rfl, hhit, hmin⟩ := in1 r hres
      refine ⟨fun r' hr' => ?_, fun hnone => ?_⟩
      · injection hr' with hr'
        exact ⟨[], x, xs, rfl, fun p hp => absurd hp (List.not_mem_nil),
          pre, j, post, hsplit, hr'.symm, hhit, hmin⟩
      · injection hnone

theorem findPair_correct (a : Array Int) (t : Int) :
    match (findPair a t).run with
    | some (i, j) => i < j ∧ j < a.size ∧ a[i]! + a[j]! = t ∧
        ∀ p q, p < q → q < a.size → a[p]! + a[q]! = t → i < p ∨ (i = p ∧ j ≤ q)
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
    obtain ⟨preI, i, postI, houtsplit, houter, pre, j, post, hinsplit, rfl, hhit, hmin⟩ := h1 r hres
    have hipos := range'_split_pos houtsplit
    have hjpos := range'_split_pos hinsplit
    have hlen : (List.range' 0 a.size).length = a.size := by simp
    have hout_len : a.size = preI.length + (postI.length + 1) := by
      simpa [houtsplit] using hlen.symm
    have hin_len : a.size - (i+1) = pre.length + (post.length + 1) := by
      have : (List.range' (i+1) (a.size - (i+1))).length = a.size - (i+1) := by simp
      simpa [hinsplit] using this.symm
    refine ⟨by omega, by omega, hhit, ?_⟩
    intro p q hpq hq hpqhit
    by_cases hpi : p < i
    · exact absurd hpqhit (houter p ((range'_split_mem_prefix houtsplit).mpr ⟨Nat.zero_le p, by omega⟩) q hpq hq)
    · by_cases hpi' : p = i
      · subst hpi'
        by_cases hqj : q < j
        · exact absurd hpqhit (hmin q ((range'_split_mem_prefix hinsplit).mpr ⟨by omega, hqj⟩))
        · exact Or.inr ⟨rfl, by omega⟩
      · exact Or.inl (by omega)

end Manual
