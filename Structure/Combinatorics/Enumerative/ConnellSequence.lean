/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ConnellSequence.lean -/

import Mathlib.Data.Finset.Image
import Def.Combinatorics.Enumerative.ConnellSequence
/-!
# Connell sequences

This file formalizes Definition 1 from Grady D. Bullington, *The Connell Sum Sequence*:
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Bullington/bullington7.tex>.
-/


namespace MetaMathlibExt

/-- Admissible parameters for a Connell `(m, r)` sequence. -/
structure ConnellParameters where
  m : ℕ
  r : ℕ
  two_le_m : 2 ≤ m
  pos_r : 0 < r

end MetaMathlibExt
