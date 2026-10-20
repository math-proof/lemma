import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProductSurjective
open scoped NumberField Valued
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct
open scoped NumberField.LiesOver
open TensorProduct
open IsDedekindDomain.HeightOneSpectrum


/--
[denseRange_algebraMap_placesOver](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
private lemma denseRange_algebraMap_placesOver_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  DenseRange (fun y : L => fun w : v.placesOver L =>
    algebraMap L (w.val.adicCompletion L) y) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap_placesOver v

/--
[denseRange_completionTensorProductMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
private lemma denseRange_completionTensorProductMap_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  DenseRange (completionTensorProductMap (K := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.denseRange_completionTensorProductMap v

/--
[completionTensorProductMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
private lemma completionTensorProductMap_surjective_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  Function.Surjective
    (completionTensorProductMap (K := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.completionTensorProductMap_surjective v


-- created on 2026-10-20
