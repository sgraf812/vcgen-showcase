import Std.Internal.Do
import Std.Tactic.Do

/-!
# Balanced brackets

Depth counting with early return on a negative dip, verified against the structurally
recursive `Bal` predicate (the `Dip` pattern from `HumanEval3`: suffix-direction
invariant, one `@[grind]` equation per step).

The loop runs over `s.toList`: hoisting the string to its character list at the
program boundary keeps the whole verification in the `List` cursor infrastructure.

## Direct `String` iteration, a spike

`for c in s` (no `toList`) is supported by the metatheory: `Spec.forIn_string` drives
the loop with a `StringInvariant s β Pred`, an invariant indexed by `String.Pos`,
entered at `s.startPos` and exited at `s.endPos`. The position-to-content bridge is
`String.Pos.Splits p t₁ t₂` (`s = t₁ ++ t₂` with `p` between), with a complete lemma
kit: `splits_startPos_iff`, `splits_endPos_iff`, `splits_next`,
`Splits.exists_eq_singleton_append`, `Splits.eq_right`.

What does not exist yet is a grind framework over that kit. Phrasing the invariant as
`fun pos st => ∀ t₁ t₂, pos.Splits t₁ t₂ → …` leaves `finish` two failure modes with
no middle ground: the quantified invariant needs ground `Splits` witnesses to
instantiate, and the witness-producing lemmas (`Pos.splits`, `splits_next_right`)
self-feed, each instance minting new positions (`pos.next`, slice positions) that
trigger the next instance, diverging at any heartbeat budget. A curated set of
terminating patterns over `Splits` is a framework-design task of its own; until it
exists, `toList` at the boundary is the way to verify string loops.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

def balanced (s : String) : Id Bool := do
  let mut depth : Int := 0
  for c in s.toList do
    if c = '(' then
      depth := depth + 1
    else if c = ')' then
      depth := depth - 1
      if depth < 0 then
        return false
  return depth = 0

/-- The bracket sequence is balanced when read at nesting depth `d`. -/
@[grind] def Bal (d : Int) : List Char → Prop
  | [] => d = 0
  | c :: cs =>
    if c = '(' then Bal (d + 1) cs
    else if c = ')' then d > 0 ∧ Bal (d - 1) cs
    else Bal d cs

theorem balanced_spec (s : String) :
    ⦃ True ⦄ balanced s ⦃ fun r => r = true ↔ Bal 0 s.toList ⦄ := by
  vcgen [balanced] invariants
  | inv1 => fun xs st => match st.1 with
    | none => st.2 ≥ 0 ∧ (Bal 0 s.toList ↔ Bal st.2 xs.suffix)
    | some false => xs.suffix = [] ∧ ¬ Bal 0 s.toList
    | some true => False
  with finish
