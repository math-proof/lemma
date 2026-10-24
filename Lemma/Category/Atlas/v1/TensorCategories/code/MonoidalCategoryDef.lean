import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.MonoidalCategoryDef
open CategoryTheory MonoidalCategory Category TensorCategories
open CategoryTheory MonoidalCategory MonoidalOpposite


/--
[Definition_1_1_1.pentagon](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean)
-/
@[path]
lemma Definition_1_1_1.pentagon
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {W X Y Z : C} :
-- imply
  (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom = (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom :=
-- proof
  MonoidalCategory.pentagon W X Y Z

namespace TensorCategories

/--
[Definition_1_2_6_pentagon](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean)
-/
@[path]
lemma Definition_1_2_6_pentagon
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {W X Y Z : C} :
-- imply
  (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom = (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom :=
-- proof
  MonoidalCategory.pentagon W X Y Z

end TensorCategories

namespace TensorCategories

/--
[Definition_1_2_6_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean)
-/
@[path]
lemma Definition_1_2_6_triangle
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X Y : C} :
-- imply
  (α_ X (𝟙_ C) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y :=
-- proof
  MonoidalCategory.triangle X Y

end TensorCategories

namespace TensorCategories

/--
[Proposition_1_2_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean)
-/
@[path]
lemma Proposition_1_2_1
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C] :
-- imply
  (∀ (X Y : C), (α_ X (𝟙_ C) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y) ∧ ((ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom) :=
-- proof
  ⟨fun X Y => MonoidalCategory.triangle X Y, unitors_equal.symm⟩

end TensorCategories

namespace TensorCategories

/--
[Definition_1_1_1_unitMorphism_eq_leftUnitor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean)
-/
@[path]
lemma Definition_1_1_1_unitMorphism_eq_leftUnitor
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C] :
-- imply
  Definition_1_1_1_unitMorphism (C := C) = (λ_ (𝟙_ C)).hom := by
-- proof
  unfold Definition_1_1_1_unitMorphism
  exact unitors_equal.symm

end TensorCategories

namespace TensorCategories

/--
[Definition_1_2_6_implies_1_1_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean)
-/
@[path]
lemma Definition_1_2_6_implies_1_1_1
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C] :
-- imply
  (∀ W X Y Z : C, (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom = (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom) ∧ (∃ _ι : (𝟙_ C) ⊗ (𝟙_ C) ≅ (𝟙_ C), True) ∧ Nonempty (tensorLeft (𝟙_ C) : C ⥤ C).IsEquivalence ∧ Nonempty (tensorRight (𝟙_ C) : C ⥤ C).IsEquivalence :=
-- proof
  ⟨fun W X Y Z => MonoidalCategory.pentagon W X Y Z,
    ⟨ρ_ (𝟙_ C), trivial⟩,
    ⟨Definition_1_1_1_leftMultEquiv⟩,
    ⟨Definition_1_1_1_rightMultEquiv⟩⟩

end TensorCategories

/--
[Definition_1_1_3.tensor_reversed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean)
-/
@[path]
lemma Definition_1_1_3.tensor_reversed
  {C : Type u'}
  [Category.{v'} C]
  [MonoidalCategory C]
  {X Y : C} :
-- imply
  (mop X ⊗ mop Y : (MonoidalOpposite C)) = mop (Y ⊗ X) :=
-- proof
  rfl

/--
[Definition_1_1_3.unit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean)
-/
@[path]
lemma Definition_1_1_3.unit_eq
  {C : Type u'}
  [Category.{v'} C]
  [MonoidalCategory C] :
-- imply
  (𝟙_ (MonoidalOpposite C)) = mop (𝟙_ C) :=
-- proof
  rfl

/--
[Definition_1_1_3.associator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean)
-/
@[path]
lemma Definition_1_1_3.associator_eq
  {C : Type u'}
  [Category.{v'} C]
  [MonoidalCategory C]
  {X Y Z : C} :
-- imply
  (α_ (mop X) (mop Y) (mop Z) : mop (Z ⊗ (Y ⊗ X)) ≅ mop ((Z ⊗ Y) ⊗ X)) = (α_ Z Y X).symm.mop :=
-- proof
  rfl


-- created on 2026-10-23
