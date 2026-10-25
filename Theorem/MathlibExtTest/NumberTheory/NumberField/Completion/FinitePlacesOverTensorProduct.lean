/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProduct.lean -/

/-
Author: @toskua, Avocado
-/


import Def.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProduct
import Lemma.Nat.NumberField.Completion.FinitePlacesOverTensorProduct
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open TensorProduct
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
variable [Algebra K L] (v : HeightOneSpectrum (𝓞 K))


noncomputable section

/-- The canonical map has the expected type. -/
example : v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K]
    ((w : v.placesOver L) → w.val.adicCompletion L) :=
  completionTensorProductMap v

/-- Evaluation projects to the component map. -/
example (t : v.adicCompletion K ⊗[K] L) (w : v.placesOver L) :
    completionTensorProductMap v t w = completionTensorProductComponent v w t :=
  rfl

/-- Pure-tensor formula through the product map. -/
example (x : v.adicCompletion K) (y : L) (w : v.placesOver L) :
    completionTensorProductMap v (x ⊗ₜ[K] y) w =
      Algebra.algHom (v.adicCompletion K) (v.adicCompletion K) (w.val.adicCompletion L) x *
        Algebra.algHom K L _ y :=
  rfl

/-- Postcomposition with evaluation recovers the component. -/
example (w : v.placesOver L) :
    (Pi.evalAlgHom (v.adicCompletion K) (fun w : v.placesOver L => w.val.adicCompletion L) w).comp
        (completionTensorProductMap (K := K) (L := L) v) =
      completionTensorProductComponent v w :=
  completionTensorProductMap_pi_eval v w

end
