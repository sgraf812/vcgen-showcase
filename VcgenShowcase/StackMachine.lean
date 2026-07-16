import Std.Internal.Do
import Std.Tactic.Do

/-!
# Compiler correctness for a stack machine

Arithmetic expressions compile to instructions for a stack machine running in
`ExceptT String (StateM (List Int))`, throwing on stack underflow.

`compile_correct` states that executing compiled code pushes the denotation. The
omitted exception postcondition defaults to `⊥`, so the theorem also proves that
compiled code never underflows.

The proof is structural induction on the expression. In each case `exec_append`
reshapes the program into sequential composition, and `vcgen` composes the induction
hypotheses (passed as spec lemmas) through the binds; `finish` closes the arithmetic.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

inductive Expr where
  | num (n : Int)
  | add (e₁ e₂ : Expr)
  | mul (e₁ e₂ : Expr)

@[grind] def Expr.denote : Expr → Int
  | .num n => n
  | .add e₁ e₂ => e₁.denote + e₂.denote
  | .mul e₁ e₂ => e₁.denote * e₂.denote

inductive Instr where
  | push (n : Int)
  | add
  | mul

abbrev StackM := ExceptT String (StateM (List Int))

def execInstr : Instr → StackM Unit
  | .push n => modify (n :: ·)
  | .add => do
    match ← get with
    | y :: x :: st => set ((x + y) :: st)
    | _ => throw "stack underflow"
  | .mul => do
    match ← get with
    | y :: x :: st => set ((x * y) :: st)
    | _ => throw "stack underflow"

def exec : List Instr → StackM Unit
  | [] => pure ()
  | i :: is => do execInstr i; exec is

def Expr.compile : Expr → List Instr
  | .num n => [.push n]
  | .add e₁ e₂ => e₁.compile ++ e₂.compile ++ [.add]
  | .mul e₁ e₂ => e₁.compile ++ e₂.compile ++ [.mul]

theorem exec_append (xs ys : List Instr) :
    exec (xs ++ ys) = (do exec xs; exec ys) := by
  induction xs with
  | nil => simp [exec]
  | cons i is ih => simp [exec, ih]

theorem compile_correct (e : Expr) (s : List Int) :
    ⦃ fun st => st = s ⦄
    exec e.compile
    ⦃ fun _ st => st = e.denote :: s ⦄ := by
  induction e generalizing s with
  | num n =>
    simp only [Expr.compile]
    vcgen [exec, execInstr] with finish
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.compile, exec_append]
    vcgen [exec, execInstr, ih₁, ih₂] with finish
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.compile, exec_append]
    vcgen [exec, execInstr, ih₁, ih₂] with finish
