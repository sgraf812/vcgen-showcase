import Std.Internal.Do
import Init.Internal.Order.While

/-!
# Shared plumbing for the manual `while`-loop baselines

`while` loops elaborate to `Lean.Loop.forIn`, which is `repeatM` of a `ForInStep`
wrapper around the body. That wrapper `match` elaborates to a fresh auxiliary matcher
in every declaration that spells it inline, which defeats `rcases`, `rw` and
unification. `wrap` names the wrapper once; `loop_forIn_eq` moves a goal from the
elaborated form onto `wrap`, and is provable only at kernel transparency
(`with_unfolding_all rfl`), the one setting that unfolds auxiliary matchers.
-/

/-- The `ForInStep` wrapper that `Lean.Loop.forIn` builds around a `while` body. -/
def wrap {β : Type} (f : Unit → β → Id (ForInStep β)) (b : β) : Id (β ⊕ β) :=
  match (f () b : Id (ForInStep β)) with
  | .done b' => pure (Sum.inr b')
  | .yield b' => pure (Sum.inl b')

theorem wrap_done {β : Type} {f : Unit → β → Id (ForInStep β)} {b b' : β}
    (h : f () b = pure (ForInStep.done b')) : wrap f b = pure (Sum.inr b') := by
  simp only [wrap, h]; rfl

theorem wrap_yield {β : Type} {f : Unit → β → Id (ForInStep β)} {b b' : β}
    (h : f () b = pure (ForInStep.yield b')) : wrap f b = pure (Sum.inl b') := by
  simp only [wrap, h]; rfl

/-- `while` loops are `repeatM` of the wrapped body. -/
theorem loop_forIn_eq {β : Type} [Nonempty β] (init : β) (f : Unit → β → Id (ForInStep β)) :
    forIn (m := Id) Lean.Loop.mk init f = repeatM (m := Id) (wrap f) init := by
  with_unfolding_all rfl
