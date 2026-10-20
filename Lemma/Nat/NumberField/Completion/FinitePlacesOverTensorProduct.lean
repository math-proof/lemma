import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProduct
open scoped NumberField
open TensorProduct
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct
open IsDedekindDomain.HeightOneSpectrum


/--
[completionTensorProductComponent_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProduct.lean)
-/
@[path]
private lemma completionTensorProductComponent_tmul_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : v.placesOver L}
  {x : v.adicCompletion K}
  {y : L} :
-- imply
  completionTensorProductComponent v w (x ⊗ₜ[K] y) =
    Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
    (w.val.adicCompletion L) x * Algebra.algHom K L _ y := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.completionTensorProductComponent_tmul v w x y

/--
[completionTensorProductMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProduct.lean)
-/
@[path]
private lemma completionTensorProductMap_apply_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {t : v.adicCompletion K ⊗[K] L}
  {w : v.placesOver L} :
-- imply
  completionTensorProductMap v t w = completionTensorProductComponent v w t := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.completionTensorProductMap_apply v t w

/--
[completionTensorProductMap_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProduct.lean)
-/
@[path]
private lemma completionTensorProductMap_tmul_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {x : v.adicCompletion K}
  {y : L}
  {w : v.placesOver L} :
-- imply
  completionTensorProductMap v (x ⊗ₜ[K] y) w =
    Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
    (w.val.adicCompletion L) x * Algebra.algHom K L _ y := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.completionTensorProductMap_tmul v x y w

/--
[completionTensorProductMap_pi_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProduct.lean)
-/
@[path]
private lemma completionTensorProductMap_pi_eval_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : v.placesOver L} :
-- imply
  (Pi.evalAlgHom (v.adicCompletion K)
    (fun w : v.placesOver L => w.val.adicCompletion L) w).comp
    (completionTensorProductMap (K := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.completionTensorProductMap_pi_eval v w


-- created on 2026-10-20
