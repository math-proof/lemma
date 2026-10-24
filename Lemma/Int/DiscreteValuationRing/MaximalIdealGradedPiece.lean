import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealGradedPiece
open IsDiscreteValuationRing


namespace IsDiscreteValuationRing

/--
[finrank_maximalIdealGradedPiece](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealGradedPiece.lean)
-/
@[path]
lemma finrank_maximalIdealGradedPiece
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {i : ℕ} :
-- imply
  Module.finrank (IsLocalRing.ResidueField R)
    (MaximalIdealGradedPiece R i) = 1 := by
-- proof
  rw [← (residueFieldLinearEquivMaximalIdealGradedPiece R i).finrank_eq]
  exact Module.finrank_self _

end IsDiscreteValuationRing


-- created on 2026-10-20
-- updated on 2026-10-23
