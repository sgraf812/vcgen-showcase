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
