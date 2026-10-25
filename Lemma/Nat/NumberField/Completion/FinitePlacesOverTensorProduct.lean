import Mathlib
import sympy.Basic
import Def.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProduct
open scoped NumberField
open TensorProduct
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct
open IsDedekindDomain.HeightOneSpectrum


namespace IsDedekindDomain.HeightOneSpectrum

/--
[completionTensorProductComponent_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProduct.lean)
-/
@[path]
lemma completionTensorProductComponent_tmul
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : v.placesOver L}
  {x : v.adicCompletion K}
  {y : L} :
-- imply
  completionTensorProductComponent v w (x ⊗ₜ[K] y) =
    Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
    (w.val.adicCompletion L) x * Algebra.algHom K L _ y :=
-- proof
  rfl

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[completionTensorProductMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProduct.lean)
-/
@[path]
lemma completionTensorProductMap_apply
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {t : v.adicCompletion K ⊗[K] L}
  {w : v.placesOver L} :
-- imply
  completionTensorProductMap v t w = completionTensorProductComponent v w t :=
-- proof
  rfl

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[completionTensorProductMap_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProduct.lean)
-/
@[path]
lemma completionTensorProductMap_tmul
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {x : v.adicCompletion K}
  {y : L}
  {w : v.placesOver L} :
-- imply
  completionTensorProductMap v (x ⊗ₜ[K] y) w =
    Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
    (w.val.adicCompletion L) x * Algebra.algHom K L _ y :=
-- proof
  rfl

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[completionTensorProductMap_pi_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProduct.lean)
-/
@[path]
lemma completionTensorProductMap_pi_eval
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : v.placesOver L} :
-- imply
  (Pi.evalAlgHom (v.adicCompletion K)
    (fun w : v.placesOver L => w.val.adicCompletion L) w).comp
    (completionTensorProductMap (K := by
-- proof
  ext t
  rfl

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-23
