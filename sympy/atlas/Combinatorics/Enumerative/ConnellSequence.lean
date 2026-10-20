/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ConnellSequence.lean -/

import Mathlib.Data.Finset.Image

/-!
# Connell sequences

This file formalizes Definition 1 from Grady D. Bullington, *The Connell Sum Sequence*:
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Bullington/bullington7.tex>.
-/

namespace MetaMathlibExt

/-- Row `j` of the Connell `(m, r)` triangle has `1 + r * (j - 1)` entries.
The source numbers rows from one; this helper is total at row zero. -/
def connellRowLength (r j : ℕ) : ℕ :=
  1 + r * (j - 1)

/-- The first entry of row `j` in the Connell `(m, r)` triangle.
The source numbers rows from one; this helper is total at row zero. -/
def connellRowStart (m r : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | j + 2 =>
      connellRowStart m r (j + 1) + m * (connellRowLength r (j + 1) - 1) + 1

/-- Entry `k`, indexed from zero, of row `j` in the Connell `(m, r)` triangle. -/
def connellEntry (m r j k : ℕ) : ℕ :=
  connellRowStart m r j + m * k

/-- The entries of row `j` in the Connell `(m, r)` triangle. -/
def connellRowEntries (m r j : ℕ) : Finset ℕ :=
  (Finset.range (connellRowLength r j)).image (connellEntry m r j)

/-- Admissible parameters for a Connell `(m, r)` sequence. -/
structure ConnellParameters where
  m : ℕ
  r : ℕ
  two_le_m : 2 ≤ m
  pos_r : 0 < r

/-- Advance one position in a row-major traversal of the Connell triangle. -/
def connellNext (r : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.2 + 1 < connellRowLength r p.1 then (p.1, p.2 + 1) else (p.1 + 1, 0)

/-- The row and zero-based column of sequence index `n` in the Connell triangle. -/
def connellPosition (r : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 => connellNext r (connellPosition r n)

/-- The Connell `(m, r)` sequence obtained by reading its triangle row by row. -/
def connellSequence (p : ConnellParameters) (n : ℕ) : ℕ :=
  let pos := connellPosition p.r n
  connellEntry p.m p.r pos.1 pos.2

end MetaMathlibExt
