/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FiniteLiesOverResidueNaturality.lean -/


import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverResidueNaturality
import Lemma.Nat.NumberField.Completion.FiniteLiesOverResidueNaturality

/-!
# Checks for the explicit residue-field naturality square
-/

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

example (a : 𝓞 K) :
    ringOfIntegersResidueQuotientMap v w (Ideal.Quotient.mk v.asIdeal a) =
      Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 K) (𝓞 L) a) := by
  unfold ringOfIntegersResidueQuotientMap
  rw [Ideal.quotientMap_mk]

example (x : v.adicCompletionIntegers K) :
    adicCompletionResidueQuotientMap v w
      (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) x) =
      Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        (adicCompletionIntegersMap v w x) := by
  unfold adicCompletionResidueQuotientMap
  rw [Ideal.quotientMap_mk]

example (q : ↥(v.adicCompletionIntegers K) ⧸
    IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers K)) :
    (ringOfIntegersResidueQuotientMap v w)
      ((completionResidueFieldEquiv v).toRingHom q) =
      (completionResidueFieldEquiv w).toRingHom
        (adicCompletionResidueQuotientMap v w q) := by
  have h :=
    DFunLike.congr_fun (completionResidueFieldEquiv_naturality v w) q
  simpa only [RingHom.comp_apply] using h

end IsDedekindDomain.HeightOneSpectrum

-- End of file.
