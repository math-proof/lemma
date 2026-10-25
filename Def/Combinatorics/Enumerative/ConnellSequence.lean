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

end MetaMathlibExt
