import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverInertiaDegree
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open scoped NumberField NumberField.LiesOver


namespace IsDedekindDomain.HeightOneSpectrum

/--
[inertiaDeg_adicCompletionIntegersMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverInertiaDegree.lean)
-/
@[path]
lemma inertiaDeg_adicCompletionIntegersMap
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).inertiaDeg
    (v.adicCompletionIntegers K) =
    w.asIdeal.inertiaDeg (𝓞 K) := by
-- proof
  have hcomp := comap_maximalIdeal_adicCompletionIntegersMap v w
  let _ : (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).LiesOver
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := ⟨hcomp.symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)),
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  apply Algebra.finrank_eq_of_equiv_equiv
    (completionResidueFieldEquiv (K := K) v)
    (completionResidueFieldEquiv (K := L) w)
  change (ringOfIntegersResidueQuotientMap v w).comp
    (completionResidueFieldEquiv (K := K) v).toRingHom =
    (completionResidueFieldEquiv (K := L) w).toRingHom.comp
      (adicCompletionResidueQuotientMap v w)
  exact completionResidueFieldEquiv_naturality v w

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-23
