import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealGradedPiece
open IsDiscreteValuationRing


/--
[finrank_maximalIdealGradedPiece](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealGradedPiece.lean)
-/
@[path]
private lemma finrank_maximalIdealGradedPiece_eq
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {i : ℕ} :
-- imply
  Module.finrank (IsLocalRing.ResidueField R)
    (MaximalIdealGradedPiece R i) = 1 := by
-- proof
  apply IsDiscreteValuationRing.finrank_maximalIdealGradedPiece R i


-- created on 2026-10-20
