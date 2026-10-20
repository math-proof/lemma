import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverResidueNaturality
open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum


/--
[completionResidueFieldEquiv_naturality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverResidueNaturality.lean)
-/
@[path]
private lemma completionResidueFieldEquiv_naturality_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  (ringOfIntegersResidueQuotientMap v w).comp
    (completionResidueFieldEquiv v).toRingHom =
    (completionResidueFieldEquiv w).toRingHom.comp
    (adicCompletionResidueQuotientMap v w) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.completionResidueFieldEquiv_naturality v w


-- created on 2026-10-20
