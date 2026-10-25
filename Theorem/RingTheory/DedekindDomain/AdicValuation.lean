/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/AdicValuation.lean -/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
/-!
# Global-local valuation ring compatibility

This file gives the precise, typed form of the identity `R_{(p)} = R_p ∩ K`: the localization
valuation subring inside a fraction field is the preimage of the valuation ring in its adic
completion along the canonical embedding.

## References

* [S. Anscombe et al., *A survey of local-global methods for Hilbert's Tenth
  Problem*](https://arxiv.org/abs/2309.14987v1)
* [G. Hu, *Anisotropy of quadratic forms over global fields of characteristic ≠ 2 is
  diophantine*](https://arxiv.org/abs/2401.00537v3)
-/


namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
end IsDedekindDomain.HeightOneSpectrum
noncomputable section

end
