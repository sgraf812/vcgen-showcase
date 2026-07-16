import VcgenShowcase.Ledger

/-!
# Transactional rollback with `try`/`catch`

`atomically` runs the ledger and restores the initial balance if any transaction
throws, giving the all-or-nothing spec: on an overdrawing list the balance is exactly
the initial one, otherwise the balance equation holds. The omitted exception
postcondition proves that `atomically` itself never throws.

The grind framework is the structurally recursive `Overdraws` predicate with two
derived rules for a variable transaction at the head of the list, each triggered on
`Overdraws b (tx :: txs)`. With those, the precise spec of `processAll` (its `epost`
characterizes exactly when it throws) is the same one-line invariant as in `Ledger`,
extended by the suffix equation `Overdraws init txs ↔ Overdraws s xs.suffix`, and the
`try`/`catch` rule composes it with the handler.

The `vcgen` list erases `applyTx_spec` (`-applyTx_spec`): the registered spec has the
trivial exception postcondition, and a registered spec shadows unfolding, so leaving
it in place makes the exception conditions unprovable.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

/-- Starting from balance `b`, applying the transactions hits an overdraft. -/
@[grind] def Overdraws (b : Int) : List Tx → Prop
  | [] => False
  | .deposit a :: txs => Overdraws (b + a) txs
  | .withdraw a :: txs => (a : Int) > b ∨ Overdraws (b - a) txs

/-- An overdraft on the head alone is an overdraft of the whole list. -/
theorem Overdraws.of_single {b : Int} {tx : Tx} {txs : List Tx}
    (h : Overdraws b [tx]) : Overdraws b (tx :: txs) := by
  cases tx <;> grind

grind_pattern Overdraws.of_single => Overdraws b (tx :: txs)

/-- Stepping over a transaction that does not overdraw on its own. -/
theorem Overdraws.cons_of_not_single {b : Int} {tx : Tx} {txs : List Tx}
    (h : ¬ Overdraws b [tx]) :
    (Overdraws b (tx :: txs) ↔ Overdraws (b + tx.delta) txs) := by
  cases tx <;> grind

grind_pattern Overdraws.cons_of_not_single => Overdraws b (tx :: txs)

def atomically (txs : List Tx) : BankM Unit := do
  let initial ← get
  try
    processAll txs
  catch _ =>
    set initial

/-- `applyTx` with the exact exception condition. -/
theorem applyTx_spec_precise (tx : Tx) (b : Int) :
    ⦃ fun s => s = b ∧ 0 ≤ b ⦄
    applyTx tx
    ⦃ fun _ s => ¬ Overdraws b [tx] ∧ s = b + tx.delta ∧ 0 ≤ s;
      epost⟨fun _ _ => Overdraws b [tx]⟩ ⦄ := by
  cases tx <;> vcgen [applyTx, -applyTx_spec] with finish

/-- `processAll` with the exact exception condition. -/
theorem processAll_spec_precise (txs : List Tx) (init : Int) :
    ⦃ fun s => s = init ∧ 0 ≤ init ⦄
    processAll txs
    ⦃ fun _ s => ¬ Overdraws init txs ∧ s = init + totalDelta txs ∧ 0 ≤ s;
      epost⟨fun _ _ => Overdraws init txs⟩ ⦄ := by
  vcgen [processAll, applyTx_spec_precise, -applyTx_spec] invariants
  | inv1 => fun xs (_ : PUnit) s =>
      s = init + totalDelta xs.prefix ∧ 0 ≤ s ∧
      (Overdraws init txs ↔ Overdraws s xs.suffix)
  with finish

/-- All-or-nothing: the rolled-back run leaves the balance untouched exactly when the
transactions overdraw. -/
theorem atomically_spec (txs : List Tx) (init : Int) :
    ⦃ fun s => s = init ∧ 0 ≤ init ⦄
    atomically txs
    ⦃ fun _ s => (Overdraws init txs → s = init) ∧
                 (¬ Overdraws init txs → s = init + totalDelta txs ∧ 0 ≤ s) ⦄ := by
  vcgen [atomically, tryCatch, processAll_spec_precise, -applyTx_spec] with finish

namespace Manual

/-! The same theorems without `vcgen`.

Places to get stuck, beyond those in `Ledger.Manual`:

1. `catch` needs its own hand-derived rule (`run_catch`): the handler splices into
   the error branch of the bind rule, and no library simp lemma evaluates
   `ExceptT.tryCatch` through a `StateT` layer.
2. The loop lemma must be re-proved from scratch: the `Ledger.Manual` one says `True`
   about the error case, and there is no way to strengthen a completed induction
   after the fact. The `vcgen` proof upgraded the invariant by one conjunct.
3. The desugared `try` sits behind the `tryCatch` method of `MonadExcept`, which
   unfolds through `tryCatchThe` before reaching `MonadExceptOf.tryCatch`; the rule
   must be stated at the method level to match the goal syntactically, and its proof
   has to name every link of that instance chain in the simp set.
-/

/-- The `catch` rule for the stack, derived by hand. -/
theorem BankM.run_catch {α : Type} (x : BankM α) (h : String → BankM α) (init : Int) :
    (((tryCatch x h : BankM α).run.run init).run : Except String α × Int) =
      match ((x.run.run init).run : Except String α × Int) with
      | (.ok a, s) => (.ok a, s)
      | (.error e, s) => (((h e).run.run s).run : Except String α × Int) := by
  rcases hx : ((x.run.run init).run : Except String α × Int) with ⟨r | e, s⟩ <;>
    · have hx' : ((StateT.run x init).run : Except String α × Int) = _ := hx
      simp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.run_mk,
        StateT.run_bind, hx']
      try rfl

private theorem loop_aux (txs : List Tx) : ∀ init : Int, 0 ≤ init →
    match ((forIn (m := BankM) txs PUnit.unit (fun tx _ => do
        applyTx tx
        pure (ForInStep.yield PUnit.unit))).run.run init).run with
    | (.ok _, s') => ¬ Overdraws init txs ∧ s' = init + totalDelta txs ∧ 0 ≤ s'
    | (.error _, _) => Overdraws init txs := by
  induction txs with
  | nil =>
    intro init hinit
    rw [List.forIn_nil]
    exact ⟨by grind, by grind, hinit⟩
  | cons tx txs ih =>
    intro init hinit
    rw [List.forIn_cons, BankM.run_seq, BankM.run_seq, applyTx_run]
    cases tx with
    | deposit a =>
      have := ih (init + a) (by omega)
      grind
    | withdraw a =>
      by_cases h : (a : Int) > init
      · simp only [if_pos h]
        grind
      · simp only [if_neg h]
        have := ih (init - a) (by omega)
        grind

theorem atomically_correct (txs : List Tx) (init : Int) (hinit : 0 ≤ init) :
    match ((atomically txs).run.run init).run with
    | (.ok _, s') => (Overdraws init txs → s' = init) ∧
                     (¬ Overdraws init txs → s' = init + totalDelta txs ∧ 0 ≤ s')
    | (.error _, _) => False := by
  unfold atomically
  rw [BankM.run_seq]
  have hget : (((get : BankM Int)).run.run init).run = (Except.ok init, init) := rfl
  simp only [hget]
  rw [BankM.run_catch]
  unfold processAll
  rw [BankM.run_seq]
  have hloop := loop_aux txs init hinit
  have hpure : ∀ s : Int, (((pure PUnit.unit : BankM PUnit)).run.run s).run = (.ok PUnit.unit, s) :=
    fun _ => rfl
  have hset : ∀ s : Int, (((set init : BankM Unit)).run.run s).run = (.ok (), init) :=
    fun _ => rfl
  grind


end Manual

/-! Sanity tests. -/
example : (((atomically [.deposit 5, .withdraw 20]).run.run 10).run
    : Except String Unit × Int) = (.ok (), 10) := by cbv
example : (((atomically [.deposit 5, .withdraw 3]).run.run 10).run
    : Except String Unit × Int) = (.ok (), 12) := by cbv
