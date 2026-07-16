import Std.Internal.Do
import Std.Tactic.Do
import VcgenShowcase.RangeSplit

/-!
# Sieve of Eratosthenes

The spec is first-principles primality: `r[k]! = true ↔ IsPrime k` for all `k ≤ n`.

The invariant vocabulary is `MarkedBelow i k`: `k` is `0`, `1`, or has a proper
divisor strictly below the cursor `i`. The outer invariant says a cell is `false`
exactly when `MarkedBelow`; the inner invariant adds the freshly marked stripe
`i ∣ k ∧ i < k ∧ k < j`.

Number theory enters through exactly three lemmas, each a few lines:

* `divisor_swap`: a multiple of `i` below `i * i` has a proper divisor below `i`
  (why starting the marking at `i * i` is sound);
* `composite_divisor`: a proper divisor of `i` transfers to any proper multiple
  (why skipping a marked `i` is sound);
* `unique_multiple`: the only multiple of `i` in `[i*m, i*m + i)` is `i*m`
  (why the stripe `k < j` advances to `k < j + i` after one mark).

Each invariant transition is a dedicated lemma (`markInv_enter`, `markInv_step`,
`markInv_exit`, `sieveInv_skip`, `sieveInv_final`), so no verification condition
ever reasons about divisibility directly; `finish` needs `range'_split_pos` to
identify the outer cursor with `2 + prefix.length`, and two hand-closed cases
remain (the final weakening and the marking step, both three-liners).
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false
set_option linter.unusedVariables false

/-- Primality, first-principles. -/
def IsPrime (k : Nat) : Prop := 2 ≤ k ∧ ∀ d, d ∣ k → d = 1 ∨ d = k

/-- Having a proper divisor strictly below the sieve cursor. -/
def MarkedBelow (i k : Nat) : Prop := k < 2 ∨ ∃ d, 2 ≤ d ∧ d < i ∧ d ∣ k ∧ d < k

theorem markedBelow_def (i k : Nat) :
    MarkedBelow i k = (k < 2 ∨ ∃ d, 2 ≤ d ∧ d < i ∧ d ∣ k ∧ d < k) := rfl

grind_pattern markedBelow_def => MarkedBelow i k

/-- A multiple of `i` below `i * i` has a proper divisor below `i`. -/
theorem divisor_swap {i k : Nat} (hdvd : i ∣ k) (hik : i < k) (hsq : k < i * i) :
    ∃ m, 2 ≤ m ∧ m < i ∧ m ∣ k ∧ m < k := by
  obtain ⟨m, rfl⟩ := hdvd
  have hi2 : 2 ≤ i := by
    rcases i with _ | _ | i <;> simp_all <;> omega
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m <;> simp_all <;> omega
  refine ⟨m, hm2, ?_, ⟨i, Nat.mul_comm i m⟩, ?_⟩
  · exact Nat.lt_of_mul_lt_mul_left hsq
  · calc m < 2 * m := by omega
      _ ≤ i * m := Nat.mul_le_mul_right m hi2

/-- A composite number transfers one of its proper divisors to any of its multiples. -/
theorem composite_divisor {i k a : Nat} (ha : 2 ≤ a) (hai : a < i) (hadvd : a ∣ i)
    (hdvd : i ∣ k) (hik : i < k) :
    ∃ m, 2 ≤ m ∧ m < i ∧ m ∣ k ∧ m < k := by
  exact ⟨a, ha, hai, Nat.dvd_trans hadvd hdvd, by
    have := Nat.le_of_dvd (by omega) (Nat.dvd_trans hadvd hdvd)
    omega⟩

/-- The unique multiple of `i` in the window `[i*m, i*m + i)`. -/
theorem unique_multiple {i m k : Nat} (hi : 0 < i) (hdvd : i ∣ k)
    (hlo : i * m ≤ k) (hhi : k < i * m + i) : k = i * m := by
  obtain ⟨q, rfl⟩ := hdvd
  have h1 : m ≤ q := Nat.le_of_mul_le_mul_left hlo hi
  have h2 : i * q < i * (m + 1) := by rw [Nat.mul_succ]; omega
  have h3 : q < m + 1 := Nat.lt_of_mul_lt_mul_left h2
  have : q = m := by omega
  rw [this]

/-- Sieve of Eratosthenes. -/
def sieve (n : Nat) : Id (Array Bool) := do
  let mut isPrime : Array Bool := .replicate (n + 1) true
  isPrime := isPrime.setIfInBounds 0 false
  isPrime := isPrime.setIfInBounds 1 false
  for i in [2:n+1] do
    if isPrime[i]! then
      let mut j := i * i
      while j ≤ n do
        isPrime := isPrime.setIfInBounds j false
        j := j + i
  return isPrime

/-- The sieve invariant for cursor `i`. -/
def SieveInv (arr : Array Bool) (n i : Nat) : Prop :=
  arr.size = n + 1 ∧ ∀ k, k ≤ n → (arr[k]! = false ↔ MarkedBelow i k)

/-- The inner marking invariant: everything below `j` that is a proper multiple
of `i` is marked, on top of `MarkedBelow i`. -/
def MarkInv (arr : Array Bool) (n i j : Nat) : Prop :=
  arr.size = n + 1 ∧
  ∀ k, k ≤ n → (arr[k]! = false ↔ (MarkedBelow i k ∨ (i ∣ k ∧ i < k ∧ k < j)))

theorem sieveInv_init (n : Nat) :
    SieveInv (((Array.replicate (n + 1) true).setIfInBounds 0 false).setIfInBounds 1 false)
      n 2 := by
  refine ⟨by simp, ?_⟩
  intro k hk
  constructor
  · intro hfalse
    by_cases h0 : k = 0
    · left; omega
    · by_cases h1 : k = 1
      · left; omega
      · exfalso
        rw [show (((Array.replicate (n + 1) true).setIfInBounds 0 false).setIfInBounds
            1 false)[k]! = true from by grind] at hfalse
        simp at hfalse
  · intro hm
    rcases hm with h2 | ⟨d, hd2, hdi, _, _⟩
    · have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl <;> grind
    · omega

/-- Entering the marking loop for a prime `i` preserves the combined invariant. -/
theorem markInv_enter {arr : Array Bool} {n i : Nat} (h : SieveInv arr n i) :
    MarkInv arr n i (i * i) := by
  obtain ⟨hsz, hinv⟩ := h
  refine ⟨hsz, fun k hk => ?_⟩
  rw [hinv k hk]
  constructor
  · exact Or.inl
  · rintro (hm | ⟨hdvd, hik, hsq⟩)
    · exact hm
    · right
      obtain ⟨m, hm2, hmi, hmdvd, hmk⟩ := divisor_swap hdvd hik hsq
      exact ⟨m, hm2, hmi, hmdvd, hmk⟩

/-- One marking step. -/
theorem markInv_step {arr : Array Bool} {n i j : Nat} (h : MarkInv arr n i j)
    (hij : i ∣ j) (hii : i * i ≤ j) (hi : 2 ≤ i) (hjn : j ≤ n) :
    MarkInv (arr.setIfInBounds j false) n i (j + i) := by
  obtain ⟨hsz, hinv⟩ := h
  refine ⟨by simp [hsz], fun k hk => ?_⟩
  by_cases hkj : k = j
  · subst hkj
    have : (arr.setIfInBounds k false)[k]! = false := by grind
    rw [this]
    simp only [true_iff]
    right
    refine ⟨hij, ?_, by omega⟩
    have h2i : 2 * i ≤ i * i := Nat.mul_le_mul_right i hi
    omega
  · have : (arr.setIfInBounds j false)[k]! = arr[k]! := by grind
    rw [this, hinv k hk]
    constructor
    · rintro (hm | ⟨hdvd, hik, hlt⟩)
      · exact Or.inl hm
      · exact Or.inr ⟨hdvd, hik, by omega⟩
    · rintro (hm | ⟨hdvd, hik, hlt⟩)
      · exact Or.inl hm
      · right
        refine ⟨hdvd, hik, ?_⟩
        rcases Nat.lt_or_ge k j with h | h
        · exact h
        · exfalso
          obtain ⟨m, rfl⟩ := hij
          exact hkj (unique_multiple (by omega) hdvd (by omega) (by omega))

/-- Leaving the marking loop advances the sieve invariant, because every proper
multiple of `i` up to `n` is either below `i * i` (divisor swap) or was marked. -/
theorem markInv_exit {arr : Array Bool} {n i j : Nat} (h : MarkInv arr n i j)
    (hstop : ¬ j ≤ n) (hij : i ∣ j) (hii : i * i ≤ j) (hi : 2 ≤ i) :
    SieveInv arr n (i + 1) := by
  obtain ⟨hsz, hinv⟩ := h
  refine ⟨hsz, fun k hk => ?_⟩
  rw [hinv k hk]
  constructor
  · rintro (hm | ⟨hdvd, hik, hlt⟩)
    · rcases hm with h2 | ⟨d, hd⟩
      · exact Or.inl h2
      · exact Or.inr ⟨d, by omega, by omega, hd.2.2⟩
    · exact Or.inr ⟨i, hi, by omega, hdvd, hik⟩
  · rintro (h2 | ⟨d, hd2, hdi, hddvd, hdk⟩)
    · exact Or.inl (Or.inl h2)
    · by_cases hdlt : d < i
      · exact Or.inl (Or.inr ⟨d, hd2, hdlt, hddvd, hdk⟩)
      · have hdeq : d = i := by omega
        subst hdeq
        right
        exact ⟨hddvd, hdk, by omega⟩

/-- Skipping a composite `i` also advances the sieve invariant: any proper
multiple of `i` inherits a smaller proper divisor from `i` itself. -/
theorem sieveInv_skip {arr : Array Bool} {n i : Nat} (h : SieveInv arr n i)
    (hi : 2 ≤ i) (hcomp : arr[i]! = true → False) (hin : i ≤ n) :
    SieveInv arr n (i + 1) := by
  obtain ⟨hsz, hinv⟩ := h
  have hmarked : MarkedBelow i i := by
    have := hinv i hin
    rcases harr : arr[i]! with _ | _
    · exact (this).mp harr
    · exact absurd harr hcomp
  refine ⟨hsz, fun k hk => ?_⟩
  rw [hinv k hk]
  constructor
  · rintro (h2 | ⟨d, hd⟩)
    · exact Or.inl h2
    · exact Or.inr ⟨d, by omega, by omega, hd.2.2⟩
  · rintro (h2 | ⟨d, hd2, hdi, hddvd, hdk⟩)
    · exact Or.inl h2
    · by_cases hdlt : d < i
      · exact Or.inr ⟨d, hd2, hdlt, hddvd, hdk⟩
      · have hdeq : d = i := by omega
        subst hdeq
        rcases hmarked with hlt | ⟨a, ha2, hai, hadvd, hak⟩
        · omega
        · right
          obtain ⟨m, hm2, hmi, hmdvd, hmk⟩ :=
            composite_divisor ha2 (by omega) hadvd hddvd hdk
          exact ⟨m, hm2, hmi, hmdvd, hmk⟩

/-- Once the cursor has passed `n`, unmarked means prime. -/
theorem sieveInv_final {arr : Array Bool} {n i : Nat} (h : SieveInv arr n i)
    (hni : n < i) :
    ∀ k, k ≤ n → (arr[k]! = true ↔ IsPrime k) := by
  obtain ⟨hsz, hinv⟩ := h
  intro k hk
  have hiff := hinv k hk
  constructor
  · intro htrue
    have hnm : ¬ MarkedBelow i k := by
      intro hm
      have := hiff.mpr hm
      simp [htrue] at this
    have h2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exact absurd (Or.inl h) hnm
      · exact h
    refine ⟨h2, fun d hdvd => ?_⟩
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · by_cases hdk : d = k
      · exact Or.inr hdk
      · exfalso
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        have hdle : d ≤ k := Nat.le_of_dvd (by omega) hdvd
        exact hnm (Or.inr ⟨d, by omega, by omega, hdvd, by omega⟩)
  · intro hp
    rcases harr : arr[k]! with _ | _
    · exfalso
      rcases hiff.mp harr with h2 | ⟨d, hd2, hdi, hddvd, hdk⟩
      · have := hp.1; omega
      · rcases hp.2 d hddvd with rfl | rfl <;> omega
    · rfl

theorem sieve_spec (n : Nat) :
    ⦃ True ⦄ sieve n
    ⦃ fun r => r.size = n + 1 ∧ ∀ k, k ≤ n → (r[k]! = true ↔ IsPrime k) ⦄ := by
  vcgen [sieve] invariants
  | inv1 => fun xs arr => SieveInv arr n (2 + xs.prefix.length)
  | inv2 cur suff hsplit s0 hinv hif => fun st => match st with
    | .inl (arr, j) => MarkInv arr n cur j ∧ cur ∣ j ∧ cur * cur ≤ j ∧ 2 ≤ cur
    | .inr (arr, j) => SieveInv arr n (cur + 1)
  | inv3 => fun st => n + 1 - st.2
  with (try finish [sieveInv_init, markInv_enter, markInv_step, markInv_exit,
    sieveInv_skip, sieveInv_final, range'_split_pos, Nat.dvd_mul_right])
  case vc2 =>
    rename_i arr hinv
    exact ⟨hinv.1, sieveInv_final hinv (by simp at hinv ⊢; omega)⟩
  case vc5 =>
    rename_i pref cur suff hsplit arr0 hsiv hif st hinv hguard
    obtain ⟨arr, j⟩ := st
    dsimp only at hinv hguard ⊢
    obtain ⟨hmark, hdvd, hii, h2⟩ := hinv
    simp only [meet_prop_eq_and]
    exact ⟨by simp; omega, markInv_step hmark hdvd hii h2 hguard,
      Nat.dvd_add hdvd (Nat.dvd_refl cur), by omega, h2⟩

/-! Sanity tests. `native_decide`: the `while` loop is an opaque fixpoint. -/
example : ((List.range 31).filter (fun k => (sieve 30).run[k]!))
    = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] := by native_decide
example : (sieve 1).run = #[false, false] := by native_decide
example : (sieve 0).run = #[false] := by native_decide
example : (sieve 2).run[2]! = true := by native_decide
example : (sieve 25).run[25]! = false := by native_decide
example : (sieve 49).run[49]! = false := by native_decide
