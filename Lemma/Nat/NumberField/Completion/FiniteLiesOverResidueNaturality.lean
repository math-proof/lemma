import Mathlib
import sympy.Basic
import Def.NumberTheory.NumberField.Completion.FiniteLiesOverResidueNaturality
open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum


namespace IsDedekindDomain.HeightOneSpectrum

/--
[completionResidueFieldEquiv_naturality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverResidueNaturality.lean)
-/
@[path]
lemma completionResidueFieldEquiv_naturality
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  (ringOfIntegersResidueQuotientMap v w).comp
    (completionResidueFieldEquiv v).toRingHom =
    (completionResidueFieldEquiv w).toRingHom.comp
    (adicCompletionResidueQuotientMap v w) := by
-- proof
  ext q
  obtain ⟨a, ha⟩ := surjective_completionResidueMap (K := K) v
    (Ideal.Quotient.mk _ q)
  simp only [RingHom.comp_apply]
  rw [← ha]
  have hdown : completionResidueFieldEquiv (K := K) v (completionResidueMap (K := K) v a) =
    Ideal.Quotient.mk v.asIdeal a := by
    simp only [completionResidueFieldEquiv, RingEquiv.trans_apply,
      RingHom.quotientKerEquivOfSurjective_symm_apply,
      Ideal.quotEquivOfEq_mk]
  have hup : completionResidueFieldEquiv (K := L) w
    (completionResidueMap (K := L) w (algebraMap (𝓞 K) (𝓞 L) a)) =
    Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 K) (𝓞 L) a) := by
    simp only [completionResidueFieldEquiv, RingEquiv.trans_apply,
      RingHom.quotientKerEquivOfSurjective_symm_apply,
      Ideal.quotEquivOfEq_mk]
  have hmid : adicCompletionResidueQuotientMap v w
    (completionResidueMap (K := K) v a) =
    completionResidueMap (K := L) w (algebraMap (𝓞 K) (𝓞 L) a) := by
    unfold adicCompletionResidueQuotientMap completionResidueMap
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk,
      adicCompletionIntegersMap_algebraMap v w a]
  have hdown' : (completionResidueFieldEquiv (K := K) v).toRingHom
    (completionResidueMap (K := K) v a) =
    Ideal.Quotient.mk v.asIdeal a := hdown
  have hup' : (completionResidueFieldEquiv (K := L) w).toRingHom
    (completionResidueMap (K := L) w (algebraMap (𝓞 K) (𝓞 L) a)) =
    Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 K) (𝓞 L) a) := hup
  simp only [hdown', hmid, hup']
  unfold ringOfIntegersResidueQuotientMap
  rw [Ideal.quotientMap_mk]

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-23
