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
| `Rollback` | transactional all-or-nothing ledger | `try`/`catch`, exact exception postconditions (`epost` characterizes when `processAll` throws), spec shadowing via `-applyTx_spec` |
| `TwoSum` | two-pointer search on a sorted array | early return from `while`, exclusion invariant, variant; baseline needs the `wrap`/`with_unfolding_all` recipe against matcher identity |

`FindIndex.Manual` holds the baselines. The idiomatic non-`vcgen` proof reflects the
loop into `List.find?` over `List.range'` and derives the spec from the `find?` API
(~30 lines); it exists because this loop coincides with a library combinator, and it
still pays the desugaring bridge, an induction for the reflection, and `Id`
definitional-unwrapping traps. `FindIndex.Manual.Raw` is the same-base
comparison: the grind-annotated `List` and `Id` lemmas, no combinator theory, no
`vcgen`. Its aux lemma hand-states what `vcgen` generates (invariant, both exit
conditions, the impossible-state clause, each repeated per conjunct), bridges the
desugaring, and normalizes the monad layer per induction step; grind closes the
leaves once the statement is phrased through `.run` so the `Id` lemmas fire, at
roughly four times the `vcgen` proof text.
For loops that accumulate state (`Ledger`, `HumanEval114`), reflection means defining
a bespoke recursive function and proving the reflection by hand; the `vcgen`
invariant is exactly that reflection, obtained for free.

Every module carries such a `Manual` namespace with the same-base baseline and a
"places to get stuck" list. The recurring taxes across them:

* A sequencing rule per transformer stack (`BankM.run_seq`, `StackM.run_seq`): the
  bind rule of the program logic, re-derived by hand before anything composes.
* The aux statement is the invariant plus both exit conditions plus the
  generalizations (start offset, consumed prefix, accumulators, fuel), with the loop
  term spelled once per conjunct.
* Elaboration identity, in three flavors: mutations become `have` bindings that make
  the goal's lambda differ syntactically from the one you would write (`HasDup`,
  `HumanEval3`); `match` expressions elaborate to per-declaration auxiliary matchers
  that `rw`, `show` and unification refuse to cross (`Isqrt`); and `simp` re-normalizes
  mid-proof so case equations stop matching and must be transported by defeq
  (`have h' : … := h`).
* The `Id` and `Except`/`State` simp APIs are keyed on `.run`, so statement phrasing
  decides whether whole lemma families fire; `match (pure x) with …` does not reduce
  syntactically at all.
* `while` loops (`Isqrt`) add fixpoint plumbing: the loop is a `repeatM` least
  fixpoint whose one sanctioned unfolding hides behind a `MonadTail` instance, and
  the termination variant becomes explicit fuel threaded through the induction.

The bottom line across all seven: the semantic work (invariants, the `afrom` and
`Dip` predicates, the grind frameworks) is identical in both worlds. What `vcgen`
deletes is a per-example tax of program-logic re-derivation and
elaboration-identity debugging, and each instance of that tax is a place where a
proof stalls for reasons unrelated to the program being verified.

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
