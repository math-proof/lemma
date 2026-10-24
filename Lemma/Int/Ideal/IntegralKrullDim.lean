import Mathlib
import sympy.Basic


/--
[ringKrullDim_le_of_integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Ideal/IntegralKrullDim.lean)
-/
@[path]
lemma ringKrullDim_le_of_integral
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] :
-- imply
  ringKrullDim B ≤ ringKrullDim A :=
-- proof
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B))
    (fun _ _ h => Ideal.IsIntegral.under_lt_under h)


-- created on 2026-10-20
-- updated on 2026-10-23
