import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.SeparableExtension
open IsDedekindDomain
open scoped NumberField NumberField.LiesOver Valued
open IsDedekindDomain.HeightOneSpectrum


/--
[separableExtension_isCompletion_finitePlace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/SeparableExtension.lean)
-/
@[path]
private lemma separableExtension_isCompletion_finitePlace_eq
  {K : Type u} [Field K] [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {M : Type v} [Field M] [Algebra (v.adicCompletion K) M] [FiniteDimensional (v.adicCompletion K) M] [Algebra.IsSeparable (v.adicCompletion K) M] :
-- imply
  ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
    (_ : Algebra.IsSeparable K L) (_ : FiniteDimensional K L)
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal),
    let _ : w.asIdeal.LiesOver v.asIdeal := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.separableExtension_isCompletion_finitePlace v M


-- created on 2026-10-20
