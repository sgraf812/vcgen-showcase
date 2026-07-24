import Std.Internal.Do
import Std.Tactic.Do
import Std.Data.HashMap

/-!
# Atomic multi-account transfers over a `HashMap` bank

A batch of transfers between named accounts, all-or-nothing via `try`/`catch`. The
spec identifies the imperative program with a pure model: `transferAllAtomic txs`
returns `true` and the state `applyTxs b txs` reaches, or returns `false` and
restores the initial bank, exactly according to whether the model succeeds.

The proof structure:

* `transfer_spec` (`@[spec]`) characterizes one transfer by one model step
  (`applyTx`), with the exception postcondition carrying the model's error.
* The loop invariant is a single fold equation, `applyTxs b xs.prefix = .ok s`.
* `applyTxs_append` splits a batch at the cursor into the prefix's result bound
  through the suffix; the `Except.bind` reductions and `applyTx_eta` (bridging the
  tuple eta-expansion the `for` destructuring introduces) let `grind` stitch every
  verification condition from the invariant.
-/

open Std.Internal.Do Lean.Order

namespace Transfer

set_option mvcgen.warning false
set_option grind.warning false
set_option linter.unusedVariables false

abbrev Bank := Std.HashMap String Int
abbrev BankM := ExceptT String (StateM Bank)

/-- A transfer order: source, destination, amount. -/
abbrev Tx := String × String × Int

def transfer (src dst : String) (amt : Int) : BankM Unit := do
  let bank ← get
  let bal := bank.getD src 0
  if bal < amt then throw "insufficient funds"
  let bank' := bank.insert src (bal - amt)
  set (bank'.insert dst (bank'.getD dst 0 + amt))

/-- Pure model of a single transfer. -/
def applyTx (b : Bank) (tx : Tx) : Except String Bank :=
  let (src, dst, amt) := tx
  let bal := b.getD src 0
  if bal < amt then .error "insufficient funds"
  else
    let b' := b.insert src (bal - amt)
    .ok (b'.insert dst (b'.getD dst 0 + amt))

/-- Pure model of a transfer batch. -/
def applyTxs (b : Bank) : List Tx → Except String Bank
  | [] => .ok b
  | tx :: txs =>
    match applyTx b tx with
    | .ok b' => applyTxs b' txs
    | .error e => .error e

@[grind =] theorem applyTxs_nil (b : Bank) : applyTxs b [] = .ok b := rfl
@[grind =] theorem applyTxs_cons (b : Bank) (tx : Tx) (txs : List Tx) :
    applyTxs b (tx :: txs) = match applyTx b tx with
      | .ok b' => applyTxs b' txs
      | .error e => .error e := rfl

@[grind =] theorem applyTx_eta (b : Bank) (tx : Tx) :
    applyTx b (tx.1, tx.2.1, tx.2.2) = applyTx b tx := rfl

/-- A batch errors as soon as a prefix errors. -/
theorem applyTxs_append_error {b : Bank} {l l' : List Tx} {e : String}
    (h : applyTxs b l = .error e) : applyTxs b (l ++ l') = .error e := by
  induction l generalizing b with
  | nil => simp [applyTxs] at h
  | cons tx txs ih =>
    rw [List.cons_append, applyTxs_cons] at *
    split at h <;> rename_i heq
    · rw [heq] at *; exact ih h
    · rw [heq] at *; exact h

/-- A batch continues from the state a prefix reaches. -/
theorem applyTxs_append_ok {b b' : Bank} {l l' : List Tx}
    (h : applyTxs b l = .ok b') : applyTxs b (l ++ l') = applyTxs b' l' := by
  induction l generalizing b with
  | nil => simp [applyTxs] at h; subst h; simp
  | cons tx txs ih =>
    rw [List.cons_append, applyTxs_cons] at *
    split at h <;> rename_i heq
    · rw [heq] at *; exact ih h
    · rw [heq] at *; exact absurd h (by simp)

@[grind =] theorem except_ok_bind {α β ε : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a).bind f = f a := rfl
@[grind =] theorem except_error_bind {α β ε : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e : Except ε α).bind f = Except.error e := rfl

/-- A batch splits at any cursor: the suffix runs from the prefix's result. -/
@[grind =] theorem applyTxs_append (b : Bank) (l l' : List Tx) :
    applyTxs b (l ++ l') = (applyTxs b l).bind (fun b' => applyTxs b' l') := by
  induction l generalizing b with
  | nil => rfl
  | cons tx txs ih =>
    simp only [List.cons_append, applyTxs_cons]
    cases applyTx b tx with
    | ok b' => simp [ih]
    | error e => rfl

@[spec] theorem transfer_spec (src dst : String) (amt : Int) (b : Bank) :
    ⦃ fun s => s = b ⦄
    transfer src dst amt
    ⦃ fun _ s => applyTx b (src, dst, amt) = .ok s;
      epost⟨fun e _ => applyTx b (src, dst, amt) = .error e⟩ ⦄ := by
  vcgen [transfer] with finish [applyTx]

/-- Apply every transfer in order; any failure aborts mid-batch. -/
def transferAll (txs : List Tx) : BankM Unit := do
  for (src, dst, amt) in txs do
    transfer src dst amt

/-- All-or-nothing batch: on failure the bank rolls back to the initial state. -/
def transferAllAtomic (txs : List Tx) : BankM Bool := do
  let saved ← get
  try
    transferAll txs
    pure true
  catch _ =>
    set saved
    pure false

theorem transferAllAtomic_spec (txs : List Tx) (b : Bank) :
    ⦃ fun s => s = b ⦄
    transferAllAtomic txs
    ⦃ fun r s => (∀ b', applyTxs b txs = .ok b' → r = true ∧ s = b') ∧
                 (∀ e, applyTxs b txs = .error e → r = false ∧ s = b) ⦄ := by
  vcgen [transferAllAtomic, tryCatch, transferAll] invariants
  | inv1 => fun xs (_ : PUnit) s => applyTxs b xs.prefix = .ok s
  with finish [applyTxs_append_error, applyTxs_append_ok]

end Transfer

/-! Sanity tests. `native_decide`: `HashMap` internals do not reduce in the kernel. -/
open Transfer in
private def bank0 : Transfer.Bank := Std.HashMap.ofList [("alice", 100), ("bob", 10)]

example : (((Transfer.transferAllAtomic [("alice", "bob", 30)]).run.run bank0).run.1.toOption)
    = some true := by native_decide
example : ((((Transfer.transferAllAtomic [("alice", "bob", 30)]).run.run bank0).run.2).getD "alice" 0)
    = 70 := by native_decide
example : ((((Transfer.transferAllAtomic [("alice", "bob", 30)]).run.run bank0).run.2).getD "bob" 0)
    = 40 := by native_decide
example : (((Transfer.transferAllAtomic [("alice", "bob", 30), ("bob", "alice", 500)]).run.run
    bank0).run.1.toOption) = some false := by native_decide
example : ((((Transfer.transferAllAtomic [("alice", "bob", 30), ("bob", "alice", 500)]).run.run
    bank0).run.2).getD "alice" 0) = 100 := by native_decide
example : ((((Transfer.transferAllAtomic [("carol", "bob", 1)]).run.run bank0).run.2).getD "bob" 0)
    = 10 := by native_decide
