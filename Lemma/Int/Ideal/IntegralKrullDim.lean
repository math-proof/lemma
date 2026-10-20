import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Ideal.IntegralKrullDim


/--
[ringKrullDim_le_of_integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Ideal/IntegralKrullDim.lean)
-/
@[path]
private lemma ringKrullDim_le_of_integral_eq
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] :
-- imply
  ringKrullDim B ≤ ringKrullDim A := by
-- proof
  apply ringKrullDim_le_of_integral


-- created on 2026-10-20
