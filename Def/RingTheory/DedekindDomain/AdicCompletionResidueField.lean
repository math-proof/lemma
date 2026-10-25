/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/AdicCompletionResidueField.lean -/

import Theorem.RingTheory.DedekindDomain.AdicCompletionIntegers
import Lemma.Int.DedekindDomain.AdicCompletionIntegers
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
/-!
# Residue field of the adic completion integers

For a Dedekind domain `A` with fraction field `K` and
`𝔭 : IsDedekindDomain.HeightOneSpectrum A`, the composite map starting at `A`,
through the `𝔭`-adic completion integers and onto the residue field of the
completion, is surjective with kernel `𝔭.asIdeal`, inducing a residue-field
ring equivalence.
-/


noncomputable section

open IsDedekindDomain

open scoped Valued

namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

variable (𝔭 : HeightOneSpectrum A)

/-- The residue-field map starting at `A`: the algebra map into the `𝔭`-adic
completion integers followed by the quotient onto the residue field of the
completion. -/
noncomputable def completionResidueMap :
    A →+* (𝔭.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) :=
  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K))).comp
    (algebraMap A (𝔭.adicCompletionIntegers K))

end IsDedekindDomain.HeightOneSpectrum
end
