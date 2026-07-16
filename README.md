# vcgen showcase

Examples of imperative Lean programs whose specs are one `vcgen ... with finish`
away, on toolchain `leanprover/lean4-nightly:nightly-2026-07-15`. `vcgen` is the
Sym-based verification condition generator over the `Std.Internal.Do` metatheory;
`finish` is the grind-mode discharge step sharing `vcgen`'s internalised E-graph.

## Examples

| Module | Program | Features |
|---|---|---|
| `FindIndex` | first index of a target in an array | `for` over a range, early return, plus the full manual proof for contrast |
| `Isqrt` | integer square root | `while` loop, invariant and termination variant, nonlinear arithmetic |
| `Ledger` | transaction processing | `ExceptT String (StateM Int)`, `@[spec]` composition, exception postcondition |
| `StackMachine` | compiler correctness | induction with `vcgen` per case, IHs as spec lemmas, no-underflow for free from the `⊥` epost |
| `HasDup` | duplicate detection | `Std.HashSet` in the loop state, closed by the library's grind API |
| `HumanEval3` | `below_zero` from human-eval-lean | replaces the upstream `HasPrefix` theory with a 3-line spec predicate |
| `HumanEval114` | `minSubArraySum` (Kadane) from human-eval-lean | one-equation loop invariant over a structurally recursive `afrom`; replaces the upstream append-direction preservation lemmas |

`FindIndex.Manual` is the honest baseline: the same theorem proved against the raw
`forIn` desugaring takes a start-offset-generalized induction over `List.range'`,
`ForInStep` state plumbing, and `Id` definitional-unwrapping traps, at roughly ten
times the proof text. For `while` loops (`Isqrt`) the baseline does not exist at all:
they elaborate to a `partial_fixpoint`, so a direct proof has to invent fixpoint
induction first.

## Recipes

**Setup.** `import Std.Internal.Do` and `Std.Tactic.Do`, then
`open Std.Internal.Do Lean.Order`. The `Lean.Order` open brings the `CompleteLattice`
instances that triple elaboration needs.

**Triples.** `⦃P⦄ prog ⦃Q⦄` defaults the exception postcondition to `⊥` (the program
provably does not throw). `⦃P⦄ prog ⦃Q; epost⟨E⟩⦄` supplies one handler per exception
layer. For state monads the assertions take the state as final argument. Pure-facing
specs about `(prog).run` enter the framework via
`generalize h : prog.run = r; apply Id.of_wp_run_eq h`.

**`for` loop invariants.** `inv1 : List.Cursor xs → β → Pred` receives the iteration
cursor (`xs.prefix` consumed, `xs.suffix` remaining) and the tuple of mutable
variables. With early return the tuple grows a leading return slot; match on `s.1` and
pin `xs.suffix = []` in the `some` branch, because the invariant is asserted at the
full cursor once the loop has returned:

```lean
| inv1 => fun xs s => match s.1 with
  | none => ‹still iterating›
  | some r => xs.suffix = [] ∧ ‹returned r›
```

**`while` loop invariants.** `inv1` matches on `.inl` (looping) vs `.inr` (exited);
`inv2` is the termination variant.

**Specs as the API of programs.** A helper called from a loop gets a `@[spec]` triple
(`Ledger.applyTx_spec`); induction hypotheses are passed to `vcgen` alongside simp
lemmas (`StackMachine.compile_correct`). Definitions the spec lookup should see
unfolded must be reduced before `vcgen` runs when they sit inside the program head's
arguments (`simp only [Expr.compile, exec_append]`).

## Making `finish` effective

The examples close with a bare `finish` because the domain notions carry a grind
framework:

* Domain functions and predicates are `@[grind]` definitions with structural
  equations (`Tx.delta`, `totalDelta`, `Expr.denote`, `Dip`).
* Specs are phrased so every verification condition is equational or linear
  arithmetic. `HumanEval3.Dip` is the model: the invariant
  `Dip 0 l ↔ Dip balance xs.suffix` steps by one `@[grind]` equation per iteration.
  The existential prefix-sum phrasing lives in a separate pure lemma
  (`dip_iff_take`), where the witness is constructed once, by hand.
* When a verification condition does need a witness, seed the E-graph with a ground
  instance via an explicit trigger: a lemma whose `grind_pattern` is the loop's cursor
  split `pref ++ cur :: suff` puts the right `take`/`sum` terms in reach.
* Extra lemmas go to the discharger inline: `with finish [List.take_of_length_le]`.

## Layout

The upstream clone in `_human-eval-lean/` is scratch material for comparison and is
not part of the build.
