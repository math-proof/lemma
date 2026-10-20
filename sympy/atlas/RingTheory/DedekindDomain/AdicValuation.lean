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

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The localization valuation subring at `v` is the preimage of the valuation ring in the adic
completion along the canonical embedding of the fraction field. -/
theorem valuationSubringAtPrime_eq_comap_adicCompletionIntegers (v : HeightOneSpectrum R) :
    (valuationSubringAtPrime (K := K) v).toSubring =
      Subring.comap (algebraMap K (adicCompletion K v))
        (adicCompletionIntegers K v).toSubring := by
  ext x
  simp only [Subring.mem_comap, ValuationSubring.mem_toSubring]
  simp only [valuationSubringAtPrime_eq_valuationSubring, Valuation.mem_valuationSubring_iff]
  rw [mem_adicCompletionIntegers]
  change (valuation K v) x ≤ 1 ↔ Valued.v (x : adicCompletion K v) ≤ 1
  rw [valuedAdicCompletion_eq_valuation']

end IsDedekindDomain.HeightOneSpectrum
