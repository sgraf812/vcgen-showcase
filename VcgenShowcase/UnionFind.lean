import Std.Internal.Do
import Std.Tactic.Do

/-!
# Union-find on an ordered forest

Parent-pointer union-find where well-formedness (`WF`) pins parents at or below
their child. That single representation choice pays for everything:

* the `find` loop's termination variant is the index itself (a non-root's parent
  is strictly smaller, so `i` decreases), making `inv2 => fun s => s` the entire
  termination argument;
* the model `rootOf` needs only `x + 1` fuel, and `rootOfAux_fuel` (fuel
  irrelevance above the start) is a strong induction over the same measure;
* `union` links the larger root under the smaller, so `WF` is preserved by
  construction.

`find_spec` returns exactly `rootOf`. `union_spec` states the algebra a client
needs: the merged forest is well-formed, `x` and `y` are connected, and every
previously existing connection survives (`rootOf_set_root`: redirecting a root
changes exactly the components that reached it). `finish` closes `union_spec`
from `union_post` alone, including the symmetric branch.

Path compression is deliberately absent: it mutates the array inside `find`,
which breaks the `parent ≤ child` measure that this module's proofs ride on, and
a rank-based variant would need a genuinely different termination story.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false
set_option linter.unusedVariables false

/-! ## Union-find, ordered-forest representation -/

/-- Well-formed parent array: parents never increase, and stay in bounds. -/
def WF (uf : Array Nat) : Prop := ∀ j, j < uf.size → uf[j]! ≤ j

theorem wf_def (uf : Array Nat) : WF uf = ∀ j, j < uf.size → uf[j]! ≤ j := rfl
grind_pattern wf_def => WF uf

/-- The root above `x`, by fuel-indexed parent chasing. -/
def rootOfAux (uf : Array Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x => if uf[x]! = x then x else rootOfAux uf fuel uf[x]!

/-- The root above `x`. Parents strictly decrease along the chain, so `x` steps
of fuel always suffice. -/
def rootOf (uf : Array Nat) (x : Nat) : Nat := rootOfAux uf (x + 1) x

@[grind =] theorem rootOfAux_zero (uf : Array Nat) (x : Nat) :
    rootOfAux uf 0 x = x := rfl
@[grind =] theorem rootOfAux_succ (uf : Array Nat) (fuel x : Nat) :
    rootOfAux uf (fuel + 1) x = if uf[x]! = x then x else rootOfAux uf fuel uf[x]! := rfl

/-- Fuel does not matter once it exceeds the start. -/
theorem rootOfAux_fuel {uf : Array Nat} (hwf : WF uf) :
    ∀ fuel x, x < uf.size → x < fuel → rootOfAux uf fuel x = rootOf uf x := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro x hx hfuel
    match fuel, hfuel with
    | fuel + 1, _ =>
      rw [rootOfAux_succ]
      unfold rootOf
      rw [rootOfAux_succ]
      by_cases hroot : uf[x]! = x
      · simp [hroot]
      · simp only [hroot, ite_false]
        have hlt : uf[x]! < x := by
          have := hwf x hx
          omega
        rw [ih fuel (by omega) uf[x]! (by omega) (by omega),
          ih x (by omega) uf[x]! (by omega) (by omega)]

/-- The one-step unfolding of `rootOf` at a non-root. -/
theorem rootOf_step {uf : Array Nat} (hwf : WF uf) {x : Nat} (hx : x < uf.size)
    (hnr : uf[x]! ≠ x) : rootOf uf x = rootOf uf uf[x]! := by
  have hlt : uf[x]! < x := by have := hwf x hx; omega
  unfold rootOf
  rw [rootOfAux_succ, if_neg hnr]
  exact rootOfAux_fuel hwf x uf[x]! (by omega) hlt

/-- Roots are fixed points. -/
theorem rootOf_root {uf : Array Nat} {x : Nat} (hroot : uf[x]! = x) :
    rootOf uf x = x := by
  unfold rootOf
  rw [rootOfAux_succ, if_pos hroot]

/-- The root above `x` is a root, at most `x`, and in bounds. -/
theorem rootOf_spec {uf : Array Nat} (hwf : WF uf) :
    ∀ x, x < uf.size → uf[rootOf uf x]! = rootOf uf x ∧ rootOf uf x ≤ x := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro hx
    by_cases hroot : uf[x]! = x
    · rw [rootOf_root hroot]
      exact ⟨hroot, Nat.le_refl _⟩
    · have hlt : uf[x]! < x := by have := hwf x hx; omega
      rw [rootOf_step hwf hx hroot]
      have := ih uf[x]! hlt (by omega)
      exact ⟨this.1, by omega⟩

/-! ## The programs -/

def find (uf : Array Nat) (x : Nat) : Id Nat := do
  let mut i := x
  while uf[i]! ≠ i do
    i := uf[i]!
  return i

def union (uf : Array Nat) (x y : Nat) : Id (Array Nat) := do
  let rx ← find uf x
  let ry ← find uf y
  if rx ≤ ry then
    return uf.setIfInBounds ry rx
  else
    return uf.setIfInBounds rx ry

@[spec] theorem find_spec (uf : Array Nat) (x : Nat) (hwf : WF uf) (hx : x < uf.size) :
    ⦃ True ⦄ find uf x
    ⦃ fun r => r = rootOf uf x ∧ uf[r]! = r ∧ r < uf.size ⦄ := by
  vcgen [find] invariants
  | inv1 => fun s => match s with
    | .inl i => rootOf uf i = rootOf uf x ∧ i < uf.size
    | .inr i => i = rootOf uf x ∧ uf[i]! = i ∧ i < uf.size
  | inv2 => fun s => s
  with (try finish [rootOf_step, rootOf_root])

/-! ## Union -/

theorem wf_set_root {uf : Array Nat} (hwf : WF uf) {r v : Nat} (hv : v ≤ r) :
    WF (uf.setIfInBounds r v) := by
  intro j hj
  by_cases hjr : j = r <;> grind

/-- Redirecting a root changes exactly the components that reached it. -/
theorem rootOf_set_root {uf : Array Nat} (hwf : WF uf) {r v : Nat}
    (hr : r < uf.size) (hroot : uf[r]! = r) (hv : v ≤ r) :
    ∀ z, z < uf.size →
      rootOf (uf.setIfInBounds r v) z
        = if rootOf uf z = r then rootOf (uf.setIfInBounds r v) r
          else rootOf uf z := by
  intro z
  induction z using Nat.strongRecOn with
  | ind z ih =>
    intro hz
    by_cases hzr : z = r
    · rw [hzr, rootOf_root hroot, if_pos rfl]
    · by_cases hznr : uf[z]! = z
      · have h1 : (uf.setIfInBounds r v)[z]! = z := by grind
        rw [rootOf_root h1, rootOf_root hznr, if_neg hzr]
      · have hlt : uf[z]! < z := by have := hwf z hz; omega
        have h1 : (uf.setIfInBounds r v)[z]! = uf[z]! := by grind
        have hwf' := wf_set_root hwf hv
        have hstep : rootOf (uf.setIfInBounds r v) z
            = rootOf (uf.setIfInBounds r v) uf[z]! := by
          rw [show rootOf (uf.setIfInBounds r v) uf[z]!
              = rootOf (uf.setIfInBounds r v) (uf.setIfInBounds r v)[z]! from by rw [h1]]
          exact rootOf_step hwf' (by grind) (by grind)
        rw [hstep, rootOf_step hwf hz hznr]
        exact ih uf[z]! hlt (by omega)

/-- After redirecting root `ry` to root `rx`, `ry`'s tree reaches `rx`. -/
theorem rootOf_set_root_self {uf : Array Nat} (hwf : WF uf) {rx ry : Nat}
    (hrx : rx < uf.size) (hry : ry < uf.size)
    (hrootx : uf[rx]! = rx) (hrooty : uf[ry]! = ry) (hle : rx ≤ ry) :
    rootOf (uf.setIfInBounds ry rx) ry = rx := by
  by_cases heq : rx = ry
  · have h1 : (uf.setIfInBounds ry rx)[ry]! = ry := by grind
    rw [rootOf_root h1, heq]
  · have h1 : (uf.setIfInBounds ry rx)[ry]! = rx := by grind
    have h2 : (uf.setIfInBounds ry rx)[rx]! = rx := by grind
    have hwf' := wf_set_root hwf hle
    rw [rootOf_step hwf' (by grind) (by grind), h1, rootOf_root h2]

/-- What `union` guarantees about the merged forest. -/
def UnionPost (uf : Array Nat) (x y : Nat) (r : Array Nat) : Prop :=
  WF r ∧ r.size = uf.size ∧
  rootOf r x = rootOf r y ∧
  (∀ z w, z < uf.size → w < uf.size → rootOf uf z = rootOf uf w →
    rootOf r z = rootOf r w)

theorem unionPost_def (uf : Array Nat) (x y : Nat) (r : Array Nat) :
    UnionPost uf x y r = (WF r ∧ r.size = uf.size ∧
      rootOf r x = rootOf r y ∧
      (∀ z w, z < uf.size → w < uf.size → rootOf uf z = rootOf uf w →
        rootOf r z = rootOf r w)) := rfl
grind_pattern unionPost_def => UnionPost uf x y r

theorem union_post {uf : Array Nat} (hwf : WF uf) {x y : Nat}
    (hx : x < uf.size) (hy : y < uf.size)
    (hle : rootOf uf x ≤ rootOf uf y) :
    UnionPost uf x y (uf.setIfInBounds (rootOf uf y) (rootOf uf x)) := by
  obtain ⟨hrootx, hxle⟩ := rootOf_spec hwf x hx
  obtain ⟨hrooty, hyle⟩ := rootOf_spec hwf y hy
  have hrxs : rootOf uf x < uf.size := by omega
  have hrys : rootOf uf y < uf.size := by omega
  have hself := rootOf_set_root_self hwf hrxs hrys hrootx hrooty hle
  have hred := rootOf_set_root hwf hrys hrooty hle
  have hrootof : ∀ z, z < uf.size →
      rootOf (uf.setIfInBounds (rootOf uf y) (rootOf uf x)) z
        = if rootOf uf z = rootOf uf y then rootOf uf x else rootOf uf z := by
    intro z hz
    rw [hred z hz, hself]
  refine ⟨wf_set_root hwf hle, by simp, ?_, ?_⟩
  · rw [hrootof x hx, hrootof y hy, if_pos rfl]
    have hrr : rootOf uf (rootOf uf x) = rootOf uf x := rootOf_root hrootx
    by_cases hxy : rootOf uf x = rootOf uf y
    · rw [if_pos hxy]
    · rw [if_neg hxy]
  · intro z w hz hw hzw
    rw [hrootof z hz, hrootof w hw, hzw]

/-- Union of two equivalence classes: the merged forest is well-formed, has the
same size, connects `x` to `y`, and preserves every existing connection. -/
theorem union_spec (uf : Array Nat) (x y : Nat) (hwf : WF uf)
    (hx : x < uf.size) (hy : y < uf.size) :
    ⦃ True ⦄ union uf x y
    ⦃ fun r => UnionPost uf x y r ⦄ := by
  vcgen [union] with (try finish [union_post])

/-! Sanity tests. `native_decide`: the `while` loop is an opaque fixpoint. -/
example : (find #[0, 1, 2, 3, 4, 5] 3).run = 3 := by native_decide
example : (find #[0, 0, 1, 2] 3).run = 0 := by native_decide
example : (union #[0, 0, 2, 2, 4] 1 3).run = #[0, 0, 0, 2, 4] := by native_decide
example : (find #[0, 0, 0, 2, 4] 3).run = 0 := by native_decide
example : (find #[0, 0, 0, 2, 4] 4).run = 4 := by native_decide
example : (union #[0, 1] 1 0).run = #[0, 0] := by native_decide
example : (union #[0, 1] 0 0).run = #[0, 1] := by native_decide
