import Std.Internal.Do
import Std.Tactic.Do

/-!
# Transaction processing over `ExceptT String (StateM Int)`

A ledger applies deposits and withdrawals to an account balance; a withdrawal beyond
the balance throws. The spec: on normal return the balance is the initial balance plus
the sum of all deltas, and it is nonnegative.

The grind framework is `Tx.delta`/`totalDelta`. The `@[spec]` triple for `applyTx`
characterizes one transaction; `vcgen` composes it through the loop, and the invariant
is the balance equation on the consumed prefix. The exception postcondition `epost⟨…⟩`
is the last component of the postcondition bracket.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

inductive Tx where
  | deposit (amount : Nat)
  | withdraw (amount : Nat)

abbrev BankM := ExceptT String (StateM Int)

def applyTx : Tx → BankM Unit
  | .deposit a => modify (fun s => s + (a : Int))
  | .withdraw a => do
    let bal ← get
    if (a : Int) > bal then
      throw "insufficient funds"
    set (bal - (a : Int))

def processAll (txs : List Tx) : BankM Unit := do
  for tx in txs do
    applyTx tx

/-- The balance change of a single transaction. -/
@[grind] def Tx.delta : Tx → Int
  | .deposit a => a
  | .withdraw a => -a

/-- The net balance change of a transaction list. -/
@[grind] def totalDelta (txs : List Tx) : Int := (txs.map Tx.delta).sum

/-- One transaction moves a nonnegative balance by its delta and keeps it nonnegative,
or throws. -/
@[spec] theorem applyTx_spec (tx : Tx) (b : Int) :
    ⦃ fun s => s = b ∧ 0 ≤ b ⦄
    applyTx tx
    ⦃ fun _ s => s = b + tx.delta ∧ 0 ≤ s; epost⟨fun _ _ => True⟩ ⦄ := by
  cases tx <;> vcgen [applyTx] with finish

theorem processAll_spec (txs : List Tx) (init : Int) :
    ⦃ fun s => s = init ∧ 0 ≤ init ⦄
    processAll txs
    ⦃ fun _ s => s = init + totalDelta txs ∧ 0 ≤ s; epost⟨fun _ _ => True⟩ ⦄ := by
  vcgen [processAll] invariants
  | inv1 => fun xs (_ : PUnit) s => s = init + totalDelta xs.prefix ∧ 0 ≤ s
  with finish

namespace Manual

/-! The success-case spec without `vcgen`, by hand-deriving the program logic for the
transformer stack: `run_seq` is the sequencing rule for `ExceptT String (StateM Int)`,
`applyTx_run` evaluates one transaction, and the loop lemma is an induction over the
transaction list with the initial balance generalized.

Places to get stuck, each absent from the `vcgen` proof:

1. Without a sequencing rule, unfolding the loop produces a tower of nested
   `StateT.run (match (StateT.run …) with …)` terms, one `Except`-split per bind;
   grind and simp both drown in it. `run_seq` must be formulated and proved first,
   which is re-deriving the bind rule of the program logic for this specific stack.
2. Evaluating one transaction is not one `rfl`: the balance check sits behind a
   `Decidable` instance, so the `get`-result must be rewritten in first and the `if`
   split propositionally, while the surrounding binds reduce definitionally.
3. The loop lemma must be stated against the desugared body (the `ForInStep.yield`
   wrapper around `applyTx`), and the trailing `pure ()` of the `do` block needs its
   own evaluation fact before the pieces compose.
-/

/-- The sequencing rule for the stack, derived by hand. -/
theorem BankM.run_seq {α β : Type} (x : BankM α) (k : α → BankM β) (init : Int) :
    (((x >>= k).run.run init).run : Except String β × Int) =
      match ((x.run.run init).run : Except String α × Int) with
      | (.ok a, s) => (((k a).run.run s).run : Except String β × Int)
      | (.error e, s) => (.error e, s) := by
  rcases h : ((x.run.run init).run : Except String α × Int) with ⟨r | e, s⟩ <;>
    simp [ExceptT.run_bind, StateT.run_bind, h]

/-- One transaction, evaluated. -/
theorem applyTx_run (tx : Tx) (init : Int) :
    (((applyTx tx).run.run init).run : Except String Unit × Int) =
      match tx with
      | .deposit a => (.ok (), init + (a : Int))
      | .withdraw a =>
        if (a : Int) > init then (.error "insufficient funds", init)
        else (.ok (), init - (a : Int)) := by
  cases tx with
  | deposit a => rfl
  | withdraw a =>
    have hget : (((get : BankM Int)).run.run init).run = (Except.ok init, init) := rfl
    simp only [applyTx, BankM.run_seq, hget]
    by_cases h : init < (a : Int)
    · simp only [if_pos h, gt_iff_lt]
      rfl
    · simp only [if_neg h, gt_iff_lt]
      rfl

@[grind =] theorem totalDelta_nil : totalDelta [] = 0 := rfl
@[grind =] theorem totalDelta_cons (tx : Tx) (txs : List Tx) :
    totalDelta (tx :: txs) = tx.delta + totalDelta txs := by
  simp [totalDelta, Int.add_comm]

private theorem loop_aux (txs : List Tx) : ∀ init : Int, 0 ≤ init →
    match ((forIn (m := BankM) txs PUnit.unit (fun tx _ => do
        applyTx tx
        pure (ForInStep.yield PUnit.unit))).run.run init).run with
    | (.ok _, s') => s' = init + totalDelta txs ∧ 0 ≤ s'
    | (.error _, _) => True := by
  induction txs with
  | nil =>
    intro init hinit
    rw [List.forIn_nil]
    exact ⟨by grind, hinit⟩
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
      · simp only [if_neg h]
        have := ih (init - a) (by omega)
        grind

theorem processAll_correct (txs : List Tx) (init : Int) (hinit : 0 ≤ init) :
    match ((processAll txs).run.run init).run with
    | (.ok _, s') => s' = init + totalDelta txs ∧ 0 ≤ s'
    | (.error _, _) => True := by
  unfold processAll
  rw [BankM.run_seq]
  have hpure : ∀ s : Int, (((pure PUnit.unit : BankM PUnit)).run.run s).run = (.ok PUnit.unit, s) :=
    fun _ => rfl
  have := loop_aux txs init hinit
  grind

end Manual

/-! Sanity tests. -/
example : (((processAll [.deposit 5, .withdraw 3]).run.run 10).run
    : Except String Unit × Int) = (.ok (), 12) := by cbv
example : (((processAll [.withdraw 20]).run.run 10).run
    : Except String Unit × Int).1 = .error "insufficient funds" := by cbv
