import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.OctagonalPyramidalComposition
open MetaMathlibExt


/--
[octagonalPyramidalNumber_eq_composition_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/OctagonalPyramidalComposition.lean)
-/
@[path]
private lemma octagonalPyramidalNumber_eq_composition_card_eq
  {k : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  (octagonalPyramidalCompositions k).card = octagonalPyramidalNumber k := by
-- proof
  apply MetaMathlibExt.octagonalPyramidalNumber_eq_composition_card k hk


-- created on 2026-10-20
