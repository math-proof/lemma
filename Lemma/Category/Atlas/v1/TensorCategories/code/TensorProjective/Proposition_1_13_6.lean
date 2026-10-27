import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TensorCategories.code.TensorProjective.DirectSummand
import Def.v1.Atlas.TensorCategories.code.TensorProjective.TensorSummand
open CategoryTheory MonoidalCategory Formalization Formalization.TensorProjective


namespace Formalization.TensorProjective.Proposition_1_13_6

/--
[projective_tensor_of_hasRightDual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorProjective/Proposition_1_13_6.lean)
-/
@[path]
lemma projective_tensor_of_hasRightDual
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {P X : C}
  [Projective P]
  [HasRightDual X]
-- given
  (hEpi : ∀ {A B : C} (f : A ⟶ B) [Epi f] (Z : C), Epi (f ▷ Z)) :
-- imply
  Projective (P ⊗ X) where factors := by
-- proof
  intro E Y f e he
  haveI := he
  let f' : P ⟶ Y ⊗ (Xᘁ : C) := (tensorRightHomEquiv P X (Xᘁ : C) Y) f
  haveI : Epi (e ▷ (Xᘁ : C)) := hEpi e (Xᘁ : C)
  obtain ⟨g', hg'⟩ := Projective.factors f' (e ▷ (Xᘁ : C))
  use (tensorRightHomEquiv P X (Xᘁ : C) E).symm g'
  apply (tensorRightHomEquiv P X (Xᘁ : C) Y).injective
  rw [tensorRightHomEquiv_naturality]
  change (tensorRightHomEquiv P X (Xᘁ : C) E)
    ((tensorRightHomEquiv P X (Xᘁ : C) E).symm g') ≫ e ▷ (Xᘁ : C) = f'
  rwa [Equiv.apply_symm_apply]

end Formalization.TensorProjective.Proposition_1_13_6


-- created on 2026-10-23
