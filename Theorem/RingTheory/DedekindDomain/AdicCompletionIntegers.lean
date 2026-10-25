/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/AdicCompletionIntegers.lean -/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
/-!
# Maximal ideal of the adic completion valuation ring

For a height-one prime `v` of a Dedekind domain `A` with fraction field `K`, the
extension of `v.asIdeal` along the canonical map into the valuation ring of the
`v`-adic completion of `K` is the maximal ideal of that valuation ring.
-/


namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
end IsDedekindDomain.HeightOneSpectrum
noncomputable section

end
