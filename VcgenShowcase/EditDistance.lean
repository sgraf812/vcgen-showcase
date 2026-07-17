import Std.Internal.Do
import Std.Tactic.Do

/-!
# Edit distance over `String` and `String.Pos`

`lev` is the exponential recursion; `editDistance` is the two-row dynamic program,
written directly against the byte-indexed `String` API. Rows are `Array Nat` indexed
by `String.Pos.offset.byteIdx`, so entry `q.offset.byteIdx` of a row for a processed
stem `sk` stores `lev sk (tailChars t q)`, the distance to the suffix of `t` at `q`.
No `String.toList` appears in the program; the multibyte test (`café` vs `cafe`)
exercises the genuinely non-unit byte strides.

The design that keeps the invariant to one equation:

* Both loops walk their string *backwards* from `endPos` via `Pos.prev`, so the
  suffix `tailChars t q` (resp. the stem `tailChars s p`) grows by *cons* at each
  step (`tailChars_prev`), matching the front-peeling shape of `lev`.
* `RowUpTo t sk row q0` is the loop invariant vocabulary: the filled region is every
  position from `q0` onward. `Row` is the fully filled special case at `startPos`
  (`row_of_upTo_startPos`). Each definition carries a `grind_pattern` equation.
* Termination is the byte offset itself: `Pos.prev` strictly decreases it
  (`byteIdx_prev_lt`), so every loop's variant is `st.…offset.byteIdx`.

Three step lemmas (`init_step`, `base_step`, `dp_step`) and one write-extends-the-row
lemma (`rowUpTo_extend`) are the whole grind framework; `finish` seeds `base_step`
and `row_of_upTo_startPos`, and the four residual verification conditions (each
loop's step, plus the initial row) are closed by name.

The position kit at the top is the reusable part: `tailChars` and its `prev`/endpoint
equations, and the bridge between `Pos` order and `byteIdx` arithmetic (`byteIdx_le`,
`byteIdx_inj`, `le_of_prev_le`) that lets `omega` reason about positions.
-/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false
set_option linter.unusedVariables false

/-! ## Levenshtein distance, the executable specification -/

def lev : List Char → List Char → Nat
  | [], t => t.length
  | _ :: s', [] => s'.length + 1
  | a :: s', b :: t' =>
    if a = b then lev s' t'
    else 1 + min (lev s' (b :: t')) (min (lev (a :: s') t') (lev s' t'))

@[grind =] theorem lev_nil_left (t : List Char) : lev [] t = t.length := by
  simp [lev]

@[grind =] theorem lev_nil_right (s : List Char) : lev s [] = s.length := by
  cases s <;> simp [lev]

@[grind =] theorem lev_cons_cons (a b : Char) (s' t' : List Char) :
    lev (a :: s') (b :: t') =
      if a = b then lev s' t'
      else 1 + min (lev s' (b :: t')) (min (lev (a :: s') t') (lev s' t')) := by
  rw [lev]

/-! ## Position kit -/

namespace String

/-- The characters of `s` from position `p` onward. -/
def tailChars (s : String) (p : s.Pos) : List Char := ((s.sliceFrom p).copy).toList

@[grind =] theorem tailChars_endPos (s : String) : tailChars s s.endPos = [] := by
  simp [tailChars, copy_sliceFrom_startPos]

@[grind =] theorem tailChars_startPos (s : String) : tailChars s s.startPos = s.toList := by
  have h1 := s.startPos.splits
  have h2 := splits_startPos s
  rw [tailChars, Pos.Splits.eq_right h1 h2]

theorem tailChars_prev {s : String} {p : s.Pos} (h : p ≠ s.startPos) :
    tailChars s (p.prev h) = (p.prev h).get (by simp) :: tailChars s p := by
  have h1 := (p.prev h).splits
  have h2 := Pos.splits_prev p h
  rw [tailChars, Pos.Splits.eq_right h1 h2]
  simp [tailChars]

grind_pattern tailChars_prev => tailChars s (p.prev h)

theorem byteIdx_prev_lt {s : String} {p : s.Pos} {h : p ≠ s.startPos} :
    (p.prev h).offset.byteIdx < p.offset.byteIdx := by
  have := Pos.prev_lt (p := p) (h := h)
  simpa [Pos.lt_iff, Pos.Raw.lt_iff] using this

theorem byteIdx_le_of_le {s : String} {p q : s.Pos} (h : p ≤ q) :
    p.offset.byteIdx ≤ q.offset.byteIdx := by
  rw [Pos.le_iff, Pos.Raw.le_iff] at h
  exact h

theorem byteIdx_le (s : String) (p : s.Pos) : p.offset.byteIdx ≤ s.utf8ByteSize :=
  p.isValid.le_utf8ByteSize

theorem byteIdx_inj {s : String} {p q : s.Pos}
    (h : p.offset.byteIdx = q.offset.byteIdx) : p = q := by
  rw [Pos.ext_iff, Pos.Raw.ext_iff]
  exact h

theorem pos_le_refl {s : String} (p : s.Pos) : p ≤ p := by
  rw [Pos.le_iff, Pos.Raw.le_iff]
  exact Nat.le_refl _

@[grind =] theorem byteIdx_offset_endPos (s : String) :
    s.endPos.offset.byteIdx = s.utf8ByteSize := by
  rw [offset_endPos, byteIdx_rawEndPos]

theorem le_of_prev_le {s : String} {p q : s.Pos} {h : p ≠ s.startPos}
    (hle : p.prev h ≤ q) (hne : q ≠ p.prev h) : p ≤ q := by
  rw [← Pos.prev_lt_iff_le (h := h), Pos.lt_iff, Pos.Raw.lt_iff]
  have h1 := byteIdx_le_of_le hle
  have h2 : q.offset.byteIdx ≠ (p.prev h).offset.byteIdx := fun he => hne (byteIdx_inj he)
  omega

end String

open String

/-! ## The row invariants -/

/-- The filled region of a row: every position from `q0` onward stores the
distance between `sk` and the corresponding suffix of `t`. -/
def RowUpTo (t : String) (sk : List Char) (row : Array Nat) (q0 : t.Pos) : Prop :=
  row.size = t.utf8ByteSize + 1 ∧
  ∀ (q : t.Pos), q0 ≤ q → row[q.offset.byteIdx]! = lev sk (tailChars t q)

/-- A fully filled row. -/
def Row (t : String) (sk : List Char) (row : Array Nat) : Prop :=
  row.size = t.utf8ByteSize + 1 ∧
  ∀ (q : t.Pos), row[q.offset.byteIdx]! = lev sk (tailChars t q)

theorem rowUpTo_def (t : String) (sk : List Char) (row : Array Nat) (q0 : t.Pos) :
    RowUpTo t sk row q0 = (row.size = t.utf8ByteSize + 1 ∧
      ∀ (q : t.Pos), q0 ≤ q → row[q.offset.byteIdx]! = lev sk (tailChars t q)) := rfl
grind_pattern rowUpTo_def => RowUpTo t sk row q0

theorem row_def (t : String) (sk : List Char) (row : Array Nat) :
    Row t sk row = (row.size = t.utf8ByteSize + 1 ∧
      ∀ (q : t.Pos), row[q.offset.byteIdx]! = lev sk (tailChars t q)) := rfl
grind_pattern row_def => Row t sk row

theorem row_of_upTo_startPos {t : String} {sk : List Char} {row : Array Nat}
    (h : RowUpTo t sk row t.startPos) : Row t sk row := by
  obtain ⟨hsz, hrow⟩ := h
  exact ⟨hsz, fun q => hrow q (by simp)⟩

/-- Writing a fresh entry at `q.prev h` extends the filled region by one position. -/
theorem rowUpTo_extend {t : String} {sk : List Char} {row : Array Nat} {q : t.Pos}
    (hrow : RowUpTo t sk row q) (h : q ≠ t.startPos) {v : Nat}
    (hv : v = lev sk (tailChars t (q.prev h))) :
    RowUpTo t sk (row.setIfInBounds (q.prev h).offset.byteIdx v) (q.prev h) := by
  obtain ⟨hsz, hfill⟩ := hrow
  refine ⟨by simp [hsz], ?_⟩
  intro q' hq'
  by_cases hq'p : q' = q.prev h
  · rw [hq'p]
    have hb : (q.prev h).offset.byteIdx < row.size := by
      have := byteIdx_le t (q.prev h); omega
    grind
  · have hqq' : q ≤ q' := le_of_prev_le hq' hq'p
    have hne : q'.offset.byteIdx ≠ (q.prev h).offset.byteIdx := by
      have h1 := byteIdx_le_of_le hqq'
      have h2 : (q.prev h).offset.byteIdx < q.offset.byteIdx := byteIdx_prev_lt
      omega
    have := hfill q' hqq'
    grind

/-! ## The program -/

def editDistance (s t : String) : Id Nat := do
  let mut row : Array Nat := Array.replicate (t.utf8ByteSize + 1) 0
  let mut q := t.endPos
  let mut len := 0
  while h : q ≠ t.startPos do
    len := len + 1
    row := row.setIfInBounds (q.prev h).offset.byteIdx len
    q := q.prev h
  let mut p := s.endPos
  let mut slen := 0
  while h : p ≠ s.startPos do
    let a := (p.prev h).get (by simp)
    slen := slen + 1
    let mut newRow := row.setIfInBounds t.utf8ByteSize slen
    let mut w := t.endPos
    while hw : w ≠ t.startPos do
      let b := (w.prev hw).get (by simp)
      let cost :=
        if b = a then row[w.offset.byteIdx]!
        else 1 + min row[(w.prev hw).offset.byteIdx]!
          (min newRow[w.offset.byteIdx]! row[w.offset.byteIdx]!)
      newRow := newRow.setIfInBounds (w.prev hw).offset.byteIdx cost
      w := w.prev hw
    row := newRow
    p := p.prev h
  return row[t.startPos.offset.byteIdx]!

/-! ## Step lemmas -/

/-- One step of the initialization loop. -/
theorem init_step {t : String} {row : Array Nat} {q : t.Pos} {len : Nat}
    (hrow : RowUpTo t [] row q) (h : q ≠ t.startPos)
    (hlen : len = (tailChars t q).length) :
    RowUpTo t [] (row.setIfInBounds (q.prev h).offset.byteIdx (len + 1)) (q.prev h) ∧
    len + 1 = (tailChars t (q.prev h)).length := by
  have hstep := tailChars_prev h
  refine ⟨rowUpTo_extend hrow h ?_, by rw [hstep]; simp [hlen]⟩
  rw [hstep, lev_nil_left]
  simp [hlen]

/-- Seeding the new row at `endPos`. -/
theorem base_step {t : String} {sk : List Char} {row : Array Nat} {a : Char}
    (hrow : Row t sk row) {slen : Nat} (hslen : slen = sk.length + 1) :
    RowUpTo t (a :: sk) (row.setIfInBounds t.utf8ByteSize slen) t.endPos := by
  obtain ⟨hsz, hfill⟩ := hrow
  refine ⟨by simp [hsz], ?_⟩
  intro q hq
  have hqe : q = t.endPos := by
    have := q.isValid.le_utf8ByteSize
    apply byteIdx_inj
    have h1 := byteIdx_le_of_le hq
    simp at h1 ⊢
    omega
  rw [hqe]
  have hb : t.utf8ByteSize < row.size := by omega
  grind

/-- One step of the inner filling loop. -/
theorem dp_step {t : String} {sk : List Char} {row newRow : Array Nat} {a : Char}
    {q : t.Pos} (hq : q ≠ t.startPos)
    (hrow : Row t sk row) (hnew : RowUpTo t (a :: sk) newRow q) :
    RowUpTo t (a :: sk)
      (newRow.setIfInBounds (q.prev hq).offset.byteIdx
        (if (q.prev hq).get (by simp) = a then row[q.offset.byteIdx]!
         else 1 + min row[(q.prev hq).offset.byteIdx]!
           (min newRow[q.offset.byteIdx]! row[q.offset.byteIdx]!)))
      (q.prev hq) := by
  obtain ⟨hsz, hfill⟩ := hrow
  obtain ⟨hsz2, hfill2⟩ := hnew
  apply rowUpTo_extend ⟨hsz2, hfill2⟩ hq
  have hstep := tailChars_prev hq
  rw [hstep, lev_cons_cons]
  have h1 := hfill q
  have h2 := hfill (q.prev hq)
  have h3 := hfill2 q (pos_le_refl q)
  rw [hstep] at h2
  grind

/-- The initial all-zero row is correct at `endPos`, where the only valid position
is `endPos` itself and both strings are empty. -/
theorem rowUpTo_init (t : String) :
    RowUpTo t [] (Array.replicate (t.utf8ByteSize + 1) 0) t.endPos := by
  refine ⟨by simp, ?_⟩
  intro q hq
  have hqe : q = t.endPos := by
    apply byteIdx_inj
    have h1 := byteIdx_le_of_le hq
    have h2 := byteIdx_le t q
    rw [byteIdx_offset_endPos] at h1 ⊢
    omega
  have hb : q.offset.byteIdx < t.utf8ByteSize + 1 := by
    have := byteIdx_le t q; omega
  rw [hqe]; grind

theorem editDistance_spec (s t : String) :
    ⦃ True ⦄ editDistance s t
    ⦃ fun r => r = lev s.toList t.toList ⦄ := by
  vcgen [editDistance] invariants
  | inv1 => fun st => match st with
    | .inl (row, q, len) => RowUpTo t [] row q ∧ len = (tailChars t q).length
    | .inr (row, q, len) => Row t [] row
  | inv2 => fun st => st.2.1.offset.byteIdx
  | inv3 => fun st => match st with
    | .inl (row, p, slen) => Row t (tailChars s p) row ∧ slen = (tailChars s p).length
    | .inr (row, p, slen) => Row t s.toList row
  | inv4 => fun st => st.2.1.offset.byteIdx
  | inv5 c1 c2 c3 c4 c5 => fun st => match st with
    | .inl (newRow, w) =>
        RowUpTo t ((c3.2.1.prev c5).get (by simp) :: tailChars s c3.2.1) newRow w
    | .inr (newRow, w) =>
        Row t ((c3.2.1.prev c5).get (by simp) :: tailChars s c3.2.1) newRow
  | inv6 => fun st => st.2.offset.byteIdx
  with (try finish [base_step, row_of_upTo_startPos])
  case vc1 => exact ⟨rowUpTo_init t, by simp [tailChars_endPos]⟩
  case vc9 =>
    rename_i st hinv hg
    obtain ⟨row, q, len⟩ := st
    dsimp only at hinv hg ⊢
    obtain ⟨hru, hlen⟩ := hinv
    obtain ⟨hstep, hlen'⟩ := init_step hru hg hlen
    show ⌜_⌝ ⊓ _
    rw [meet_prop_eq_and, ofProp_prop_eq]
    exact ⟨byteIdx_prev_lt (h := hg), hstep, hlen'⟩
  case vc6 =>
    rename_i c1 c2 c3 c4 c5 st hinv hg
    obtain ⟨newRow, w⟩ := st
    dsimp only at hinv hg ⊢
    obtain ⟨hrow, -⟩ := c4
    show ⌜_⌝ ⊓ _
    rw [meet_prop_eq_and, ofProp_prop_eq]
    exact ⟨byteIdx_prev_lt (h := hg), dp_step hg hrow hinv⟩
  case vc5 =>
    rename_i c1 c2 c3 c4 c5 st hinv
    obtain ⟨newRow, w⟩ := st
    dsimp only at hinv c4 ⊢
    obtain ⟨-, hslen⟩ := c4
    show ⌜_⌝ ⊓ _
    rw [meet_prop_eq_and, ofProp_prop_eq]
    refine ⟨byteIdx_prev_lt (h := c5), ?_, ?_⟩
    · rwa [tailChars_prev c5]
    · rw [tailChars_prev c5]; simp [hslen]

/-! Sanity tests. `lev` reduces in the kernel; the program needs `native_decide`. -/
example : lev "kitten".toList "sitting".toList = 3 := by cbv
example : (editDistance "kitten" "sitting").run = 3 := by native_decide
example : (editDistance "flaw" "lawn").run = 2 := by native_decide
example : (editDistance "" "").run = 0 := by native_decide
example : (editDistance "abc" "abc").run = 0 := by native_decide
example : (editDistance "abc" "").run = 3 := by native_decide
example : (editDistance "" "abc").run = 3 := by native_decide
example : (editDistance "ab" "ba").run = 2 := by native_decide
example : (editDistance "café" "cafe").run = 1 := by native_decide
