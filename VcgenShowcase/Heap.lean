import Std.Internal.Do
import Std.Tactic.Do
import VcgenShowcase.RangeSplit

/-!
# Array-backed binary min-heap with a multiset model, and heapsort

Three layers, each proved with one `vcgen` call:

* `Heap.insert` pushes and sifts up; `insert_spec` says the result is a heap, a
  permutation of `a.push x`, and one element larger.
* `Heap.extractMin` swaps the root to the back, pops it, and sifts down;
  `extractMin_spec` says the returned element is a lower bound for every member,
  the remaining array is a heap, and pushing the element back is a permutation of
  the input.
* `Heap.heapsort` builds a heap by folding `insert` and drains it with
  `extractMin`; `heapsort_spec` is full sortedness plus permutation. Its proof
  never mentions `parent`, sift invariants, or array indices: both loop bodies are
  handled by the registered `@[spec]` triples, so the invariant speaks only in the
  model vocabulary (permutations, `Pairwise`, a pointwise bound between the drained
  prefix and the remaining heap).

The grind framework:

* Index arithmetic without division: `parent_left`/`parent_right` as rewrite rules,
  `parent_lt` for termination, and `parent_cases` (every non-root index is a left or
  right child) seeded on the pattern `parent j`. All four are one-line `omega` facts;
  with them, no verification condition ever reasons about `(i - 1) / 2`.
* `IsHeap` and the sift invariants stated over `getElem!` so the library's
  `swapIfInBounds` grind API applies; each sift step is a dedicated lemma
  (`siftUpInv_swap`, `siftDownInv_swap`) whose case split (the swapped edge, the
  hole's children, the hole's siblings, everything else) is a `by_cases` skeleton
  with a `grind` leaf per case.
* `smallerChild` returns the child to descend into; `smallerChild_some` and
  `smallerChild_none` characterize it, and `smallerChild_getD` keys those facts on the
  loop guard `(smallerChild arr i).isSome`, so the sift-down step closes under `finish`.
* The heapsort drain step speaks in the model vocabulary through three grind facts:
  `drain_perm` for the permutation rotation `out ++ [m] ++ b ~ out ++ hp`,
  `drain_pairwise` for the `Pairwise` extension of the sorted prefix, and
  `push_perm_mem` for membership transport across the extracted minimum.

Every verification condition closes under `finish`.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false
set_option linter.unusedVariables false

/-! ## Index arithmetic -/

/-- Parent index in the implicit binary tree. -/
def parent (i : Nat) : Nat := (i - 1) / 2

@[grind =] theorem parent_left (i : Nat) : parent (2 * i + 1) = i := by
  unfold parent; omega

@[grind =] theorem parent_right (i : Nat) : parent (2 * i + 2) = i := by
  unfold parent; omega

theorem parent_lt {i : Nat} (h : 0 < i) : parent i < i := by
  unfold parent; omega

grind_pattern parent_lt => parent i

/-- Every non-root index is the left or right child of its parent. -/
theorem parent_cases {j : Nat} (h : 0 < j) :
    j = 2 * parent j + 1 ∨ j = 2 * parent j + 2 := by
  unfold parent; omega

grind_pattern parent_cases => parent j

/-! ## The heap predicate -/

/-- Min-heap: every non-root element is at least its parent. -/
def IsHeap (a : Array Int) : Prop :=
  ∀ j, 0 < j → j < a.size → a[parent j]! ≤ a[j]!

theorem isHeap_def (a : Array Int) :
    IsHeap a = ∀ j, 0 < j → j < a.size → a[parent j]! ≤ a[j]! := rfl

grind_pattern isHeap_def => IsHeap a

/-- The root of a min-heap is a lower bound for every element. -/
theorem IsHeap.root_le {a : Array Int} (h : IsHeap a) :
    ∀ j, j < a.size → a[0]! ≤ a[j]! := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact Int.le_refl _
    · have h1 := h j hpos hj
      have h2 := ih (parent j) (parent_lt hpos) (Nat.lt_trans (parent_lt hpos) hj)
      omega

/-- The root of a min-heap is a lower bound for every member. -/
theorem IsHeap.min_le_mem {a : Array Int} (h : IsHeap a) :
    ∀ y ∈ a.toList, a[0]! ≤ y := by
  intro y hy
  rw [List.mem_iff_getElem] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  have := h.root_le j (by simpa using hj)
  grind

/-! ## Insertion -/

namespace Heap

def insert (a : Array Int) (x : Int) : Id (Array Int) := do
  let mut arr := a.push x
  let mut i := arr.size - 1
  while 0 < i ∧ arr[i]! < arr[parent i]! do
    arr := arr.swapIfInBounds (parent i) i
    i := parent i
  return arr

/-- The sift-up invariant: heap everywhere except the edge into `i`, and the hole's
parent bounds the hole's children. -/
def SiftUpInv (arr : Array Int) (i : Nat) : Prop :=
  i < arr.size ∧
  (∀ j, 0 < j → j < arr.size → j ≠ i → arr[parent j]! ≤ arr[j]!) ∧
  (0 < i → ∀ j, j < arr.size → parent j = i → arr[parent i]! ≤ arr[j]!)

theorem siftUpInv_swap {arr : Array Int} {i : Nat}
    (hinv : SiftUpInv arr i) (hpos : 0 < i) (hlt : arr[i]! < arr[parent i]!) :
    SiftUpInv (arr.swapIfInBounds (parent i) i) (parent i) := by
  obtain ⟨hi, hexc, hhole⟩ := hinv
  have hp : parent i < arr.size := Nat.lt_trans (parent_lt hpos) hi
  refine ⟨by grind, ?_, ?_⟩
  · intro j hj hjs hjp
    by_cases hji : j = i
    · subst hji; grind
    · by_cases hjpar : parent j = i
      · grind
      · by_cases hjparp : parent j = parent i
        · have := hexc j hj (by grind) hji
          have := hexc i hpos hi
          grind
        · grind
  · intro hppos j hjs hjp
    have hplt := parent_lt hppos
    have hilt := parent_lt hpos
    have hpp : parent (parent i) < arr.size := by omega
    have h1 := hexc (parent i) hppos hp (by omega)
    by_cases hji : j = i
    · grind
    · have hj0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · exfalso; rw [show parent 0 = 0 from rfl] at hjp; omega
        · exact hj
      have hjs' : j < arr.size := by simpa using hjs
      have hjne : j ≠ parent i := by
        intro hj; rw [hj] at hjp
        have : parent (parent i) < parent i := parent_lt (by omega)
        omega
      have h2 := hexc j hj0 hjs' hji
      grind

theorem siftUpInv_push {a : Array Int} (x : Int) (h : IsHeap a) :
    SiftUpInv (a.push x) a.size := by
  refine ⟨by simp, ?_, ?_⟩
  · intro j hj hjs hjne
    have hjlt : j < a.size := by simp at hjs; omega
    have hplt : parent j < a.size := by have := parent_lt hj; omega
    have := h j hj hjlt
    grind
  · intro hpos j hjs hjp
    exfalso
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [show parent 0 = 0 from rfl] at hjp; omega
      · exact hj
    have := parent_lt hj0
    simp at hjs
    omega

theorem siftUpInv_exit {arr : Array Int} {i : Nat}
    (hinv : SiftUpInv arr i) (hstop : ¬ (0 < i ∧ arr[i]! < arr[parent i]!)) :
    IsHeap arr := by
  obtain ⟨hi, hexc, hhole⟩ := hinv
  intro j hj hjs
  by_cases hji : j = i
  · subst hji
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · omega
    · have := hexc
      grind
  · exact hexc j hj hjs hji

@[spec] theorem insert_spec (a : Array Int) (x : Int) (h : IsHeap a) :
    ⦃ True ⦄ insert a x
    ⦃ fun r => IsHeap r ∧ r.Perm (a.push x) ∧ r.size = a.size + 1 ⦄ := by
  vcgen [Heap.insert] invariants
  | inv1 => fun s => match s with
    | .inl (arr, i) => SiftUpInv arr i ∧ arr.Perm (a.push x) ∧ arr.size = a.size + 1
    | .inr (arr, i) => IsHeap arr ∧ arr.Perm (a.push x) ∧ arr.size = a.size + 1
  | inv2 => fun s => s.2
  with finish [siftUpInv_push, siftUpInv_swap, siftUpInv_exit, Array.Perm.refl]

/-! ## Extraction -/

/-- The smaller out-of-order child of `i`, if any. -/
def smallerChild (a : Array Int) (i : Nat) : Option Nat :=
  if 2 * i + 2 < a.size ∧ a[2 * i + 2]! < a[2 * i + 1]! then
    if a[2 * i + 2]! < a[i]! then some (2 * i + 2) else none
  else if 2 * i + 1 < a.size then
    if a[2 * i + 1]! < a[i]! then some (2 * i + 1) else none
  else none

theorem smallerChild_some {a : Array Int} {i c : Nat}
    (h : smallerChild a i = some c) :
    c < a.size ∧ parent c = i ∧ i < c ∧ a[c]! < a[i]! ∧
    (∀ j, j < a.size → parent j = i → 0 < j → a[c]! ≤ a[j]!) := by
  unfold smallerChild at h
  refine ⟨?_, ?_, ?_, ?_, fun j hj hjp hj0 => ?_⟩ <;>
    rcases parent_cases (j := c) (by grind) with hc | hc <;> grind

theorem smallerChild_none {a : Array Int} {i : Nat}
    (h : smallerChild a i = none) :
    ∀ j, j < a.size → parent j = i → 0 < j → a[i]! ≤ a[j]! := by
  intro j hj hjp hj0
  unfold smallerChild at h
  rcases parent_cases hj0 with hcase | hcase <;> grind

theorem smallerChild_isSome {a : Array Int} {i : Nat}
    (h : (smallerChild a i).isSome = true) :
    smallerChild a i = some ((smallerChild a i).getD 0) := by
  cases hc : smallerChild a i <;> simp_all

/-- Characterization of the descent target keyed on `isSome`, so grind derives the
target's bounds, parent, and minimality directly from the loop guard. -/
theorem smallerChild_getD {a : Array Int} {i : Nat}
    (h : (smallerChild a i).isSome = true) :
    (smallerChild a i).getD 0 < a.size ∧
      parent ((smallerChild a i).getD 0) = i ∧
      i < (smallerChild a i).getD 0 ∧
      a[(smallerChild a i).getD 0]! < a[i]! ∧
      (∀ j, j < a.size → parent j = i → 0 < j → a[(smallerChild a i).getD 0]! ≤ a[j]!) :=
  smallerChild_some (smallerChild_isSome h)

grind_pattern smallerChild_getD => (smallerChild a i).isSome

/-- The sift-down invariant: heap everywhere except the edges out of `i`, and the
hole's parent bounds the hole's children. -/
def SiftDownInv (arr : Array Int) (i : Nat) : Prop :=
  (∀ j, 0 < j → j < arr.size → parent j ≠ i → arr[parent j]! ≤ arr[j]!) ∧
  (0 < i → ∀ j, j < arr.size → parent j = i → arr[parent i]! ≤ arr[j]!)

theorem siftDownInv_start {a : Array Int} (h : IsHeap a) :
    SiftDownInv ((a.swapIfInBounds 0 (a.size - 1)).pop) 0 := by
  refine ⟨?_, fun h0 => absurd h0 (by omega)⟩
  intro j hj hjs hjp
  have hjs' : j < a.size - 1 := by simpa using hjs
  have hplt : parent j < j := parent_lt hj
  have hp0 : 0 < parent j := by
    rcases Nat.eq_zero_or_pos (parent j) with h0 | hp
    · exact absurd h0 hjp
    · exact hp
  have := h j hj (by omega)
  grind

theorem siftDownInv_swap {arr : Array Int} {i c : Nat}
    (hinv : SiftDownInv arr i) (hsc : smallerChild arr i = some c) :
    SiftDownInv (arr.swapIfInBounds i c) c := by
  obtain ⟨hexc, hhole⟩ := hinv
  obtain ⟨hcs, hpc, hic, hclt, hcmin⟩ := smallerChild_some hsc
  have his : i < arr.size := by omega
  constructor
  · intro j hj hjs hjp
    have hjs' : j < arr.size := by simpa using hjs
    by_cases hji : j = i
    · subst hji
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · omega
      · have := hhole hpos c hcs hpc
        have hpne : parent j ≠ j := by have := parent_lt hpos; omega
        have hpnec : parent j ≠ c := by have := parent_lt hpos; omega
        grind
    · by_cases hjc : j = c
      · subst hjc
        have : parent j = i := hpc
        grind
      · by_cases hjp' : parent j = i
        · have := hcmin j hjs' hjp' hj
          grind
        · have := hexc j hj hjs' hjp'
          have hpi : parent j ≠ i := hjp'
          grind
  · intro hc0 j hjs hjp
    have hjs' : j < arr.size := by simpa using hjs
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exfalso; rw [show parent 0 = 0 from rfl] at hjp; omega
      · exact hj
    have hjgt : c < j := by have := parent_lt hj0; omega
    have := hexc j hj0 hjs' (by omega)
    grind

theorem siftDownInv_exit {arr : Array Int} {i : Nat}
    (hinv : SiftDownInv arr i) (h : ¬ (smallerChild arr i).isSome = true) :
    IsHeap arr := by
  have hn : smallerChild arr i = none := by
    cases hc : smallerChild arr i
    · rfl
    · rw [hc] at h; simp at h
  intro j hj hjs
  by_cases hp : parent j = i
  · have := smallerChild_none hn j hjs hp hj
    grind
  · exact hinv.1 j hj hjs hp

/-- Removing the last element and re-adding it is the identity. -/
theorem pop_push_back {xs : Array Int} (h : 0 < xs.size) :
    xs.pop.push xs[xs.size - 1]! = xs := by
  ext i hi₁ hi₂ <;> grind

def extractMin (a : Array Int) : Id (Option (Int × Array Int)) := do
  if a.size = 0 then return none
  let m := a[0]!
  let mut arr := (a.swapIfInBounds 0 (a.size - 1)).pop
  let mut i := 0
  while (smallerChild arr i).isSome do
    let c := (smallerChild arr i).getD 0
    arr := arr.swapIfInBounds i c
    i := c
  return some (m, arr)

/-- Every permutation of the swapped-and-popped array recovers `a` when the root
is pushed back. -/
theorem push_root_perm {a arr : Array Int} (hsz : 0 < a.size)
    (hp : arr.Perm ((a.swapIfInBounds 0 (a.size - 1)).pop)) :
    (arr.push a[0]!).Perm a := by
  have hsz' : (a.swapIfInBounds 0 (a.size - 1)).size = a.size := by simp
  have hswap : (a.swapIfInBounds 0 (a.size - 1))[(a.swapIfInBounds 0 (a.size - 1)).size - 1]!
      = a[0]! := by grind
  have hback : ((a.swapIfInBounds 0 (a.size - 1)).pop.push a[0]!)
      = a.swapIfInBounds 0 (a.size - 1) := by
    rw [← hswap]
    exact pop_push_back (by simp; omega)
  have hperm2 : (a.swapIfInBounds 0 (a.size - 1)).Perm a := by
    rw [Array.swapIfInBounds_def, dif_pos (by omega), dif_pos (by omega)]
    exact Array.swap_perm (by omega) (by omega)
  have h1 := Array.Perm.push a[0]! hp
  rw [hback] at h1
  exact h1.trans hperm2

set_option maxHeartbeats 1000000 in
@[spec] theorem extractMin_spec (a : Array Int) (h : IsHeap a) :
    ⦃ True ⦄ extractMin a
    ⦃ fun r => match r with
      | none => a.size = 0
      | some (m, b) => IsHeap b ∧ (b.push m).Perm a ∧ b.size + 1 = a.size ∧
          ∀ y ∈ a.toList, m ≤ y ⦄ := by
  vcgen [Heap.extractMin] invariants
  | inv1 => fun s => match s with
    | .inl (arr, i) => SiftDownInv arr i ∧
        arr.Perm ((a.swapIfInBounds 0 (a.size - 1)).pop) ∧ arr.size + 1 = a.size
    | .inr (arr, i) => IsHeap arr ∧
        arr.Perm ((a.swapIfInBounds 0 (a.size - 1)).pop) ∧ arr.size + 1 = a.size
  | inv2 => fun s => s.1.size - s.2
  with finish [siftDownInv_start, siftDownInv_swap, siftDownInv_exit,
    smallerChild_isSome, push_root_perm, IsHeap.min_le_mem, Array.Perm.refl]

/-! ## Heapsort -/

/-- The drain-step permutation: appending the extracted minimum to the sorted prefix
and keeping the remaining heap permutes the same multiset. -/
theorem drain_perm {out hp b : List Int} {m : Int} {a : List Int}
    (hb : (b ++ [m]).Perm hp) (hperm : (out ++ hp).Perm a) :
    ((out ++ [m]) ++ b).Perm a := by
  rw [List.append_assoc]
  exact (List.Perm.append_left out ((List.perm_append_comm).trans hb)).trans hperm

grind_pattern drain_perm => ((out ++ [m]) ++ b).Perm a, (b ++ [m]).Perm hp

/-- Membership transported across the drain step: the extracted minimum and every
element of the remaining heap belong to the heap it came from. -/
theorem push_perm_mem {b hp : List Int} {m : Int} (h : (b ++ [m]).Perm hp) :
    m ∈ hp ∧ ∀ y ∈ b, y ∈ hp :=
  ⟨h.mem_iff.mp (by simp), fun y hy => h.mem_iff.mp (List.mem_append_left _ hy)⟩

grind_pattern push_perm_mem => (b ++ [m]).Perm hp

/-- The drain step keeps the sorted prefix sorted: the extracted minimum bounds every
element already drained. -/
theorem drain_pairwise {out hp : List Int} {m : Int}
    (hsort : out.Pairwise (· ≤ ·)) (hbound : ∀ x ∈ out, ∀ y ∈ hp, x ≤ y)
    (hmem : m ∈ hp) :
    (out ++ [m]).Pairwise (· ≤ ·) := by
  rw [List.pairwise_append]
  refine ⟨hsort, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
  rw [List.mem_singleton.mp hy]
  exact hbound x hx m hmem

grind_pattern drain_pairwise => (out ++ [m]).Pairwise (· ≤ ·), m ∈ hp

def heapsort (a : Array Int) : Id (Array Int) := do
  let mut hp := #[]
  for x in a do
    hp ← insert hp x
  let mut out := #[]
  while 0 < hp.size do
    match ← extractMin hp with
    | some (m, b) =>
      out := out.push m
      hp := b
    | none => pure ()
  return out

theorem heapsort_spec (a : Array Int) :
    ⦃ True ⦄ heapsort a
    ⦃ fun r => r.toList.Perm a.toList ∧ r.toList.Pairwise (· ≤ ·) ⦄ := by
  vcgen [Heap.heapsort] invariants
  | inv1 => fun xs hp => IsHeap hp ∧ hp.toList.Perm xs.prefix
  | inv2 => fun s => match s with
    | .inl (hp, out) => IsHeap hp ∧ (out.toList ++ hp.toList).Perm a.toList ∧
        out.toList.Pairwise (· ≤ ·) ∧ (∀ x ∈ out.toList, ∀ y ∈ hp.toList, x ≤ y)
    | .inr (hp, out) => out.toList.Perm a.toList ∧ out.toList.Pairwise (· ≤ ·)
  | inv3 => fun s => s.1.size
  with finish (instances := 5000) [Array.perm_iff_toList_perm, Array.Perm.refl,
    List.Pairwise.nil, List.mem_singleton]

end Heap

/-! Sanity tests. `native_decide`: the `while` loops do not reduce in the kernel. -/
example : (Heap.insert #[1, 3, 2] 0).run = #[0, 1, 2, 3] := by native_decide
example : (Heap.insert #[] 5).run = #[5] := by native_decide
example : (Heap.insert #[1, 3, 2] 4).run = #[1, 3, 2, 4] := by native_decide
example : (Heap.extractMin #[1, 3, 2]).run = some (1, #[2, 3]) := by native_decide
example : (Heap.extractMin (#[] : Array Int)).run = none := by native_decide
example : (Heap.heapsort #[3, 1, 2]).run = #[1, 2, 3] := by native_decide
example : (Heap.heapsort #[5, 4, 3, 2, 1]).run = #[1, 2, 3, 4, 5] := by native_decide
example : (Heap.heapsort #[]).run = #[] := by native_decide
example : (Heap.heapsort #[2, 1, 2, 1]).run = #[1, 1, 2, 2] := by native_decide
example : (Heap.heapsort #[0, -5, 3, -5]).run = #[-5, -5, 0, 3] := by native_decide
example : (Heap.heapsort #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]).run =
    #[1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by native_decide
