import Std.Internal.Do
import Std.Tactic.Do

/-!
# HumanEval 3: `below_zero`

The imperative solution from `leanprover/human-eval-lean`, verified with `vcgen`.

The spec predicate `Dip` is structurally recursive, so its `@[grind]` equations let
`finish` reason about the loop step purely equationally: the invariant says the answer
for the whole list equals the answer for the remaining suffix started at the current
balance. No witness for the dipping prefix is ever synthesized inside the loop proof.

`dip_iff_take` and `belowZero_iff_take` recover the prefix-sum phrasing used upstream;
they are pure list lemmas, independent of the program.

Upstream (`HumanEvalLean/HumanEval3.lean`) proves `belowZero_iff_take` via `mvcgen`
plus a bespoke `List.HasPrefix` theory of five `@[grind]` lemmas about prefix
predicates under `cons` and `append`.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

def belowZero (operations : List Int) : Bool := Id.run do
  let mut balance := 0
  for op in operations do
    balance := balance + op
    if balance < 0 then
      return true
  return false

/-- Starting from balance `b`, running some nonempty prefix of the operations ends
below zero. -/
@[grind] def Dip (b : Int) : List Int → Prop
  | [] => False
  | x :: xs => b + x < 0 ∨ Dip (b + x) xs

theorem belowZero_iff {l : List Int} : belowZero l = true ↔ Dip 0 l := by
  generalize h : belowZero l = res
  apply Id.of_wp_run_eq h
  vcgen [belowZero] invariants
  | inv1 => fun xs s => match s.1 with
    | none => Dip 0 l ↔ Dip s.2 xs.suffix
    | some true => xs.suffix = [] ∧ Dip 0 l
    | some false => False
  with finish

theorem dip_iff_take {l : List Int} {b : Int} :
    Dip b l ↔ ∃ n, n < l.length ∧ b + (l.take (n + 1)).sum < 0 := by
  induction l generalizing b with
  | nil => simp [Dip]
  | cons x xs ih =>
    simp only [Dip, ih]
    constructor
    · rintro (h | ⟨n, hlt, hn⟩)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨n + 1, by simp only [List.length_cons]; omega, by simpa [Int.add_assoc] using hn⟩
    · rintro ⟨n, hlt, hn⟩
      match n with
      | 0 => simp at hn; omega
      | m + 1 =>
        rw [List.take_succ_cons, List.sum_cons, ← Int.add_assoc] at hn
        by_cases hbx : b + x < 0
        · exact .inl hbx
        · exact .inr ⟨m, by simp only [List.length_cons] at hlt; omega, hn⟩

theorem belowZero_iff_take {l : List Int} :
    belowZero l = true ↔ ∃ n, (l.take n).sum < 0 := by
  rw [belowZero_iff, dip_iff_take]
  constructor
  · rintro ⟨n, hlt, hn⟩
    exact ⟨n + 1, by simpa using hn⟩
  · rintro ⟨n, hn⟩
    match n with
    | 0 => simp at hn
    | m + 1 =>
      by_cases hle : m < l.length
      · exact ⟨m, hle, by simpa using hn⟩
      · have hlen : l.length ≤ m + 1 := by omega
        rw [List.take_of_length_le hlen] at hn
        have hne : l ≠ [] := by rintro rfl; simp at hn
        refine ⟨l.length - 1, by have := List.length_pos_iff.mpr hne; omega, ?_⟩
        rw [Nat.sub_add_cancel (List.length_pos_iff.mpr hne), List.take_length]
        simpa using hn
