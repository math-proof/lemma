/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ConnellSequence.lean -/

import Mathlib.Data.Finset.Image
import Structure.Combinatorics.Enumerative.ConnellSequence
/-!
# Connell sequences

This file formalizes Definition 1 from Grady D. Bullington, *The Connell Sum Sequence*:
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Bullington/bullington7.tex>.
-/


namespace MetaMathlibExt

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
