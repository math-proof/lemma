import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.RigidMonoidalDuality
open CategoryTheory MonoidalCategory Limits MonoidalOpposite Opposite TensorCategories


namespace TensorCategories

/--
[whiskerRight_evaluation_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidMonoidalDuality.lean)
-/
@[path]
lemma whiskerRight_evaluation_injective
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X Y₁ Y₂ : C}
  {p₂ : ExactPairing X Y₂}
  {f g : Y₁ ⟶ Y₂}
-- given
  (h : f ▷ X ≫ p₂.evaluation = g ▷ X ≫ p₂.evaluation) :
-- imply
  f = g := by
-- proof
  suffices recover : ∀ (φ : Y₁ ⟶ Y₂),
    φ = (ρ_ Y₁).inv ≫ Y₁ ◁ p₂.coevaluation ≫ (α_ Y₁ X Y₂).inv ≫
      (φ ▷ X ≫ p₂.evaluation) ▷ Y₂ ≫ (λ_ Y₂).hom by
    rw [recover f, h, ← recover g]
  intro φ
  rw [comp_whiskerRight]; simp only [Category.assoc]
  slice_rhs 3 4 => rw [← associator_inv_naturality_left]
  slice_rhs 2 3 => rw [whisker_exchange]
  slice_rhs 1 2 => rw [← rightUnitor_inv_naturality]
  slice_rhs 3 5 => rw [p₂.coevaluation_evaluation]
  simp

end TensorCategories

namespace TensorCategories

/--
[whiskerLeft_evaluation_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidMonoidalDuality.lean)
-/
@[path]
lemma whiskerLeft_evaluation_injective
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X₁ X₂ Y : C}
  {p₂ : ExactPairing X₂ Y}
  {f g : X₁ ⟶ X₂}
-- given
  (h : Y ◁ f ≫ p₂.evaluation = Y ◁ g ≫ p₂.evaluation) :
-- imply
  f = g := by
-- proof
  suffices recover : ∀ (φ : X₁ ⟶ X₂),
    φ = (λ_ X₁).inv ≫ p₂.coevaluation ▷ X₁ ≫ (α_ X₂ Y X₁).hom ≫
      X₂ ◁ (Y ◁ φ ≫ p₂.evaluation) ≫ (ρ_ X₂).hom by
    rw [recover f, h, ← recover g]
  intro φ
  rw [MonoidalCategory.whiskerLeft_comp]; simp only [Category.assoc]
  slice_rhs 3 4 => rw [← associator_naturality_right]
  slice_rhs 2 3 => rw [← whisker_exchange]
  slice_rhs 1 2 => rw [← leftUnitor_inv_naturality]
  slice_rhs 3 5 => rw [p₂.evaluation_coevaluation]
  simp
set_option maxHeartbeats 800000 in

end TensorCategories

namespace TensorCategories

/--
[rightDualIso_hom_comp_evaluation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidMonoidalDuality.lean)
-/
@[path]
lemma rightDualIso_hom_comp_evaluation
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X Y₁ Y₂ : C}
  {p₁ : ExactPairing X Y₁}
  {p₂ : ExactPairing X Y₂} :
-- imply
  (rightDualIso p₁ p₂).hom ▷ X ≫ p₂.evaluation = p₁.evaluation := by
-- proof
  have key := @rightAdjointMate_comp_evaluation C _ _ X X
    (HasRightDual.mk (rightDual := Y₂) (exact := p₂))
    (HasRightDual.mk (rightDual := Y₁) (exact := p₁))
    (𝟙 X)
  simp only [whiskerLeft_id, Category.id_comp] at key
  exact key
set_option maxHeartbeats 800000 in

end TensorCategories

namespace TensorCategories

/--
[leftDualIso_hom_comp_evaluation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidMonoidalDuality.lean)
-/
@[path]
lemma leftDualIso_hom_comp_evaluation
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X₁ X₂ Y : C}
  {p₁ : ExactPairing X₁ Y}
  {p₂ : ExactPairing X₂ Y} :
-- imply
  Y ◁ (leftDualIso p₁ p₂).hom ≫ p₂.evaluation = p₁.evaluation := by
-- proof
  have key := @leftAdjointMate_comp_evaluation C _ _ Y Y
    (HasLeftDual.mk (leftDual := X₂) (exact := p₂))
    (HasLeftDual.mk (leftDual := X₁) (exact := p₁))
    (𝟙 Y)
  simp only [id_whiskerRight, Category.id_comp] at key
  exact key

end TensorCategories

namespace TensorCategories

/--
[Proposition_1_10_4_rightDual_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidMonoidalDuality.lean)
-/
@[path]
lemma Proposition_1_10_4_rightDual_unique
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X Y₁ Y₂ : C}
  {p₁ : ExactPairing X Y₁}
  {p₂ : ExactPairing X Y₂} :
-- imply
  ∃! (f : Y₁ ⟶ Y₂), IsIso f ∧ f ▷ X ≫ p₂.evaluation = p₁.evaluation := by
-- proof
  refine ⟨(rightDualIso p₁ p₂).hom,
    ⟨inferInstance, rightDualIso_hom_comp_evaluation p₁ p₂⟩, ?_⟩
  intro g ⟨_, hg⟩
  exact whiskerRight_evaluation_injective p₂
    (hg.trans (rightDualIso_hom_comp_evaluation p₁ p₂).symm)
end Formula_1_10_5
section Formula_1_10_6
end Formula_1_10_6
section Prop_1_10_7

end TensorCategories

namespace TensorCategories

/--
[prop_1_10_7i_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidMonoidalDuality.lean)
-/
@[path]
lemma prop_1_10_7i_right
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X Y Z : C}
  [HasRightDual X]
  [HasRightDual Y]
  [HasRightDual Z]
  {f : X ⟶ Y}
  {g : Y ⟶ Z} :
-- imply
  (f ≫ g)ᘁ = gᘁ ≫ fᘁ :=
-- proof
  comp_rightAdjointMate

end TensorCategories


-- created on 2026-10-23
