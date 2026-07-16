import Std.Internal.Do
import Std.Tactic.Do

/-!
# HumanEval 114: `minSubArraySum`

Kadane's algorithm for the minimum subarray sum, verified against the spec of
`leanprover/human-eval-lean`.

`afrom s l` is the functional core of the loop: the minimum over `0` and all sums of
subarrays of `l` that are nonempty or extend the carried suffix sum `s`. The loop
invariant is a single equation, `min minSum (afrom s cur.suffix) = afrom 0 xs.toList`,
and its preservation is one `afrom_cons` unfolding, discharged by `finish`.

The pure theory characterizes `afrom` by structural induction in the cons direction,
where `take`/`drop` reduce by one equation per step: bounds (`afrom_le_carry`,
`afrom_le_sub`), attainment (`afrom_mem`), and the packaging
`isMinSubarraySum₀_afrom`. The endgame lemmas that split on the sign of the loop
result are ported from the upstream file.

Upstream (`HumanEvalLean/HumanEval114.lean`) proves the invariant preservation in the
append direction, through `IsMinSuffixSum₀` and two `@[grind =>]` preservation lemmas
for `xs ++ [x]` of about seventy-five lines.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

/-! ## Implementation (verbatim from human-eval-lean) -/

def minSubarraySum (xs : Array Int) : Int := Id.run do
  let mut minSum := 0
  let mut s := 0
  for num in xs do
      s := min 0 (s + num)
      minSum := min s minSum
  if minSum < 0 then
      return minSum
  else
      return xs.toList.min?.getD 0

example : minSubarraySum #[2, 3, 4, 1, 2, 4] = 1 := by decide
example : minSubarraySum #[-1, -2, -3] = -6 := by decide
example : minSubarraySum #[-1, -2, -3, 2, -10] = -14 := by decide
example : minSubarraySum #[0, 10, 20, 1000000] = 0 := by decide
example : minSubarraySum #[100, -33, 32, -1, 0, -2] = -33 := by decide
example : minSubarraySum #[7] = 7 := by decide
example : minSubarraySum #[1, -1] = -1 := by decide

/-! ## Spec (verbatim from human-eval-lean) -/

def IsMinSubarraySum₀ (xs : List Int) (s : Int) : Prop :=
  (∃ (i j : Nat), i ≤ j ∧ j ≤ xs.length ∧ s = xs[i...j].toList.sum) ∧
    (∀ (i j : Nat), i ≤ j → j ≤ xs.length → s ≤ xs[i...j].toList.sum)

def IsMinSubarraySum (xs : List Int) (s : Int) : Prop :=
  if xs = [] then s = 0 else
    (∃ (i j : Nat), i < j ∧ j ≤ xs.length ∧ s = xs[i...j].toList.sum) ∧
      (∀ (i j : Nat), i < j → j ≤ xs.length → s ≤ xs[i...j].toList.sum)

/-! ## The Kadane functional -/

def afrom (s : Int) : List Int → Int
  | [] => 0
  | x :: xs => min (min 0 (s + x)) (afrom (min 0 (s + x)) xs)

@[grind =] theorem afrom_nil (s : Int) : afrom s [] = 0 := rfl
@[grind =] theorem afrom_cons (s x : Int) (xs : List Int) :
    afrom s (x :: xs) = min (min 0 (s + x)) (afrom (min 0 (s + x)) xs) := rfl

theorem afrom_nonpos (s : Int) (l : List Int) : afrom s l ≤ 0 := by
  fun_induction afrom s l with grind [afrom]

theorem afrom_le_head (s x : Int) (xs : List Int) : afrom s (x :: xs) ≤ s + x := by
  rw [afrom_cons]
  exact Int.le_trans (Int.min_le_left _ _) (Int.min_le_right _ _)

theorem afrom_le_tail (s x : Int) (xs : List Int) :
    afrom s (x :: xs) ≤ afrom (min 0 (s + x)) xs := by
  rw [afrom_cons]
  exact Int.min_le_right _ _

theorem afrom_le_carry {l : List Int} {s : Int} :
    ∀ j, 1 ≤ j → j ≤ l.length → afrom s l ≤ s + (l.take j).sum := by
  fun_induction afrom s l with grind [afrom, List.take_cons]

theorem afrom_le_sub {l : List Int} {s : Int} (hs : s ≤ 0) :
    ∀ i j, i ≤ j → j ≤ l.length → afrom s l ≤ ((l.take j).drop i).sum := by
  induction l generalizing s with
  | nil => intro i j h1 h2; simp at h2; simp [h2]; grind
  | cons x xs ih =>
    intro i j h1 h2
    rcases Nat.eq_zero_or_pos (j - i) with hji | hji
    · rw [List.drop_eq_nil_of_le (by simp; omega), List.sum_nil]
      exact afrom_nonpos s _
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [List.take_succ_cons]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [List.drop_zero, List.sum_cons]
        rcases Nat.eq_zero_or_pos j' with rfl | hj'
        · have := afrom_le_head s x xs
          simp; omega
        · have h3 := afrom_le_carry (l := xs) (s := min 0 (s + x)) j' hj' (by simpa using h2)
          have h4 := afrom_le_tail s x xs
          have h5 : min 0 (s + x) ≤ x := Int.le_trans (Int.min_le_right _ _) (by omega)
          omega
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [List.drop_succ_cons]
        have h3 := ih (s := min 0 (s + x)) (Int.min_le_left _ _) i' j' (by omega) (by simpa using h2)
        have h4 := afrom_le_tail s x xs
        omega

theorem afrom_mem {l : List Int} {s : Int} (hs : s ≤ 0) :
    afrom s l = 0 ∨
    (∃ j, 1 ≤ j ∧ j ≤ l.length ∧ afrom s l = s + (l.take j).sum) ∨
    (∃ i j, i < j ∧ j ≤ l.length ∧ afrom s l = ((l.take j).drop i).sum) := by
  induction l generalizing s with
  | nil => exact .inl rfl
  | cons x xs ih =>
    have hs' : min 0 (s + x) ≤ 0 := Int.min_le_left _ _
    rcases Int.le_total (afrom (min 0 (s + x)) xs) (min 0 (s + x)) with hA | hA
    · have heq : afrom s (x :: xs) = afrom (min 0 (s + x)) xs := by
        rw [afrom_cons]; omega
      rcases ih (s := min 0 (s + x)) hs' with h0 | ⟨j, hj1, hj2, hj⟩ | ⟨i, j, hij, hj2, hj⟩
      · exact .inl (heq.trans h0)
      · rcases Int.le_total (s + x) 0 with hsx | hsx
        · refine .inr (.inl ⟨j + 1, by omega, by simpa using hj2, ?_⟩)
          rw [List.take_succ_cons, List.sum_cons, heq, hj, Int.min_eq_right hsx]
          omega
        · refine .inr (.inr ⟨1, j + 1, by omega, by simpa using hj2, ?_⟩)
          rw [List.take_succ_cons, List.drop_succ_cons, List.drop_zero, heq, hj,
            Int.min_eq_left hsx]
          omega
      · refine .inr (.inr ⟨i + 1, j + 1, by omega, by simpa using hj2, ?_⟩)
        rw [List.take_succ_cons, List.drop_succ_cons, heq, hj]
    · have heq : afrom s (x :: xs) = min 0 (s + x) := by
        rw [afrom_cons]; omega
      rcases Int.le_total (s + x) 0 with hsx | hsx
      · refine .inr (.inl ⟨1, by omega, by simp, ?_⟩)
        rw [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, heq,
          Int.min_eq_right hsx]
        omega
      · exact .inl (heq.trans (Int.min_eq_left hsx))

/-- `afrom 0 l` is the minimum sum over possibly empty subarrays. -/
theorem isMinSubarraySum₀_afrom (l : List Int) : IsMinSubarraySum₀ l (afrom 0 l) := by
  constructor
  · rcases afrom_mem (l := l) (s := 0) (Int.le_refl 0) with h0 | ⟨j, hj1, hj2, hj⟩ | ⟨i, j, hij, hj2, hj⟩
    · exact ⟨0, 0, by omega, by omega, by simpa [List.toList_mkSlice_rco] using h0⟩
    · exact ⟨0, j, by omega, hj2, by simpa [List.toList_mkSlice_rco] using hj⟩
    · exact ⟨i, j, by omega, hj2, by simpa [List.toList_mkSlice_rco] using hj⟩
  · intro i j hij hj
    simpa [List.toList_mkSlice_rco] using afrom_le_sub (l := l) (s := 0) (Int.le_refl 0) i j hij hj

/-! ## Endgame lemmas (ported from human-eval-lean) -/

attribute [local grind =] List.toList_mkSlice_rco List.le_min_iff
attribute [local grind →] List.mem_of_mem_take List.mem_of_mem_drop

@[grind →]
theorem isMinSubarraySum₀_le_zero {xs : List Int} {s : Int} :
    IsMinSubarraySum₀ xs s → s ≤ 0 := by
  intro h
  have := h.2 0 0
  grind [IsMinSubarraySum₀]

theorem isMinSubarraySum_of_isMinSubarraySum₀_of_neg {xs : List Int} {s : Int} (hs : s < 0) :
    IsMinSubarraySum₀ xs s → IsMinSubarraySum xs s := by
  grind [IsMinSubarraySum, IsMinSubarraySum₀, List.drop_take_self]

theorem List.length_mul_le_sum {xs : List Int} {m : Int} (h : ∀ x, x ∈ xs → m ≤ x) :
    xs.length * m ≤ xs.sum := by
  induction xs
  · grind
  · rename_i x xs ih
    simp only [List.mem_cons, forall_eq_or_imp, List.length_cons] at *
    grind

theorem isMinSubarraySum_of_nonneg {xs : List Int} {minSum : Int}
    (h : IsMinSubarraySum₀ xs minSum) (hs : minSum ≥ 0) :
    IsMinSubarraySum xs (xs.min?.getD 0) := by
  rw [IsMinSubarraySum]
  split
  · simp [*]
  · have : minSum = 0 := by grind
    have := this
    rw [List.min?_eq_some_min (by grind), Option.getD_some]
    have hmin : xs.min (by grind) = xs.min (by grind) := rfl
    rw [List.min_eq_iff, List.mem_iff_getElem] at hmin
    have : 0 ≤ xs.min (by grind) := by
      false_or_by_contra
      obtain ⟨i, _, hi⟩ := hmin.1
      have := h.2 i (i + 1) (by grind) (by grind)
      simp only [List.toList_mkSlice_rco, List.take_add_one] at this
      grind
    apply And.intro
    · obtain ⟨i, _, hi⟩ := hmin.1
      exact ⟨i, i + 1, by grind, by grind, by grind [List.take_add_one]⟩
    · intro i j hi hj
      have : ∀ a, a ∈ (xs.take j).drop i → xs.min (by grind) ≤ a := by grind
      have := List.length_mul_le_sum this
      simp only [List.toList_mkSlice_rco, *]
      refine Int.le_trans ?_ this
      rw (occs := [1]) [show ∀ h, xs.min h = 1 * xs.min h by grind]
      apply Int.mul_le_mul <;> grind

/-! ## Main theorem -/

theorem isMinSubarraySum_minSubarraySum {xs : Array Int} :
    IsMinSubarraySum xs.toList (minSubarraySum xs) := by
  generalize hwp : minSubarraySum xs = w
  apply Id.of_wp_run_eq hwp
  vcgen [minSubarraySum] invariants
  | inv1 => fun cur (st : Int × Int) =>
      min st.1 (afrom st.2 cur.suffix) = afrom 0 xs.toList ∧ st.2 ≤ 0 ∧ st.1 ≤ 0
  with finish [afrom_nonpos, isMinSubarraySum₀_afrom,
    isMinSubarraySum_of_isMinSubarraySum₀_of_neg, isMinSubarraySum_of_nonneg]

namespace Manual

/-! The same theorem without `vcgen`. The loop has no early return, so the aux lemma
is a single equation: starting from accumulators `(ms, s)`, the loop computes
`min ms (afrom s l)`. The `afrom` theory and the endgame lemmas are shared with the
`vcgen` proof; what is added is the loop reflection and the plumbing to reach it:
the `Array`-to-`List` `forIn` bridge, pushing `Id.run` through the binds, and one
defeq transport of the loop equation onto the goal's `have`-normalized lambda. -/

set_option linter.unusedVariables false

private theorem loop_aux (l : List Int) : ∀ ms s : Int, s ≤ 0 → ms ≤ 0 →
    (forIn (m := Id) l ((ms, s) : Int × Int) (fun num st =>
      pure (.yield (min (min 0 (st.2 + num)) st.1, min 0 (st.2 + num))))).run.1 =
      min ms (afrom s l) := by
  induction l with
  | nil =>
    intro ms s hs hms
    rw [List.forIn_nil]
    simp only [afrom_nil, Id.run_pure]
    omega
  | cons x xs ih =>
    intro ms s hs hms
    rw [List.forIn_cons]
    simp only [pure_bind]
    rw [ih (min (min 0 (s + x)) ms) (min 0 (s + x)) (by omega) (by omega), afrom_cons]
    omega

theorem minSubarraySum_eq_afrom (xs : Array Int) :
    minSubarraySum xs =
      if afrom 0 xs.toList < 0 then afrom 0 xs.toList else xs.toList.min?.getD 0 := by
  have key : (forIn (m := Id) xs (((0 : Int), (0 : Int)) : Int × Int) (fun num __s =>
      have minSum := __s.fst
      have s := __s.snd
      have s := min 0 (s + num)
      have minSum := min s minSum
      pure (ForInStep.yield (minSum, s)))).run.1 = min 0 (afrom 0 xs.toList) := by
    rw [← Array.forIn_toList]
    exact loop_aux xs.toList 0 0 (by omega) (by omega)
  unfold minSubarraySum
  simp only [bind]
  have key' : (forIn (m := Id) xs (((0 : Int), (0 : Int)) : Int × Int) (fun num __s =>
      pure (.yield (min (min 0 (__s.snd + num)) __s.fst, min 0 (__s.snd + num))))).fst =
      min 0 (afrom 0 xs.toList) := key
  rw [key', Int.min_eq_right (afrom_nonpos 0 xs.toList)]
  split <;> simp

theorem isMinSubarraySum_minSubarraySum (xs : Array Int) :
    IsMinSubarraySum xs.toList (minSubarraySum xs) := by
  rw [minSubarraySum_eq_afrom]
  have h₀ := isMinSubarraySum₀_afrom xs.toList
  split
  · exact isMinSubarraySum_of_isMinSubarraySum₀_of_neg (by assumption) h₀
  · exact isMinSubarraySum_of_nonneg h₀ (by grind [afrom_nonpos])

end Manual
