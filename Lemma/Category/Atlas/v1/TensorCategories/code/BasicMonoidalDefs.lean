import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.TensorCategories.code.BasicMonoidalDefs.Part5
open CategoryTheory MonoidalCategory Category TensorCategories


namespace TensorCategories

/--
[prop_1_2_2_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasicMonoidalDefs.lean)
-/
@[path]
lemma prop_1_2_2_left
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {X Y : C} :
-- imply
  (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom = (λ_ X).hom ▷ Y := by
-- proof
  rw [leftUnitor_tensor_hom, Iso.hom_inv_id_assoc]

end TensorCategories

namespace TensorCategories

/--
[unitors_inv_equal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasicMonoidalDefs.lean)
-/
@[path]
lemma unitors_inv_equal
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C] :
-- imply
  (λ_ (𝟙_ C : C)).inv = (ρ_ (𝟙_ C : C)).inv := by
-- proof
  rw [← cancel_mono (λ_ (𝟙_ C : C)).hom, Iso.inv_hom_id, unitors_equal, Iso.inv_hom_id]

end TensorCategories

namespace TensorCategories

/--
[rightUnitor_conjugate_whiskerRight_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasicMonoidalDefs.lean)
-/
@[path]
lemma rightUnitor_conjugate_whiskerRight_unit
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
-- given
  (h : (𝟙_ C : C) ⟶ 𝟙_ C) :
-- imply
  h ▷ 𝟙_ C = (ρ_ (𝟙_ C)).hom ≫ h ≫ (ρ_ (𝟙_ C)).inv := by
-- proof
  have nat := rightUnitor_naturality h
  calc h ▷ 𝟙_ C
    = h ▷ 𝟙_ C ≫ (ρ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv := by simp
    _ = (ρ_ (𝟙_ C)).hom ≫ h ≫ (ρ_ (𝟙_ C)).inv := by rw [← assoc, nat, assoc]

end TensorCategories

namespace TensorCategories

/--
[rightUnitor_conjugate_whiskerLeft_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasicMonoidalDefs.lean)
-/
@[path]
lemma rightUnitor_conjugate_whiskerLeft_unit
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
-- given
  (h : (𝟙_ C : C) ⟶ 𝟙_ C) :
-- imply
  𝟙_ C ◁ h = (ρ_ (𝟙_ C)).hom ≫ h ≫ (ρ_ (𝟙_ C)).inv := by
-- proof
  have nat := leftUnitor_naturality h
  calc 𝟙_ C ◁ h
    = 𝟙_ C ◁ h ≫ (λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv := by simp
    _ = (λ_ (𝟙_ C)).hom ≫ h ≫ (λ_ (𝟙_ C)).inv := by rw [← assoc, nat, assoc]
    _ = (ρ_ (𝟙_ C)).hom ≫ h ≫ (ρ_ (𝟙_ C)).inv := by rw [unitors_equal, unitors_inv_equal]

end TensorCategories

namespace TensorCategories

/--
[prop_1_2_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasicMonoidalDefs.lean)
-/
@[path]
lemma prop_1_2_7
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {f g : (𝟙_ C : C) ⟶ 𝟙_ C} :
-- imply
  f ≫ g = g ≫ f := by
-- proof
  have expand1 : f ⊗ₘ g = (ρ_ (𝟙_ C)).hom ≫ (f ≫ g) ≫ (ρ_ (𝟙_ C)).inv := by
    rw [MonoidalCategory.tensorHom_def,
      rightUnitor_conjugate_whiskerRight_unit f,
      rightUnitor_conjugate_whiskerLeft_unit g]; simp [assoc]
  have expand2 : f ⊗ₘ g = (ρ_ (𝟙_ C)).hom ≫ (g ≫ f) ≫ (ρ_ (𝟙_ C)).inv := by
    rw [tensorHom_def',
      rightUnitor_conjugate_whiskerLeft_unit g,
      rightUnitor_conjugate_whiskerRight_unit f]; simp [assoc]
  have := expand1.symm.trans expand2
  simp [cancel_epi] at this
  exact this

end TensorCategories

namespace TensorCategories

/--
[Proposition_1_2_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasicMonoidalDefs.lean)
-/
@[path]
lemma Proposition_1_2_7
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {f g : (𝟙_ C : C) ⟶ 𝟙_ C} :
-- imply
  f ≫ g = g ≫ f :=
-- proof
  prop_1_2_7 f g

end TensorCategories


-- created on 2026-10-23
