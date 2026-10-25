/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean -/

/-
Author: @toskua, Avocado
-/


import Def.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProductSurjective
import Lemma.Nat.NumberField.Completion.FinitePlacesOverTensorProductSurjective
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
variable [Algebra K L] (v : HeightOneSpectrum (𝓞 K))


noncomputable section

example : DenseRange (fun y : L => fun w : v.placesOver L =>
    algebraMap L (w.val.adicCompletion L) y) :=
  denseRange_algebraMap_placesOver v

example : DenseRange (completionTensorProductMap (K := K) (L := L) v) :=
  denseRange_completionTensorProductMap v

example : Function.Surjective
    (completionTensorProductMap (K := K) (L := L) v) :=
  completionTensorProductMap_surjective v

example (t : (w : v.placesOver L) → w.val.adicCompletion L) :
    ∃ s, completionTensorProductMap (K := K) (L := L) v s = t :=
  completionTensorProductMap_surjective v t

end
