import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.MonoidalFunctorProps.Part2
open TensorCategories TensorCategories.MonoidalFunctorProps
open CategoryTheory MonoidalCategory Functor
open Category


namespace TensorCategories.MonoidalFunctorProps

/--
[Prop_1_4_3_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorProps.lean)
-/
@[path]
lemma Prop_1_4_3_left
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {D : Type u₂}
  [Category.{v₂} D]
  [MonoidalCategory D]
  {F : C ⥤ D}
  [F.LaxMonoidal]
  {X : C} :
-- imply
  (λ_ (F.obj X)).hom = LaxMonoidal.ε F ▷ F.obj X ≫ LaxMonoidal.μ F (𝟙_ C) X ≫ F.map (λ_ X).hom :=
-- proof
  LaxMonoidal.left_unitality F X

end TensorCategories.MonoidalFunctorProps

/--
[monoidalNatTrans_tensorHom_comp_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorProps.lean)
-/
@[path]
private lemma monoidalNatTrans_tensorHom_comp_eval_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {D : Type u₂}
  [Category.{v₂} D]
  [MonoidalCategory D]
  {F G : C ⥤ D}
  [F.Monoidal]
  [G.Monoidal]
  {α : F ⟶ G}
  [α.IsMonoidal]
  {X Y : C}
  [ExactPairing X Y] :
-- imply
  (α.app Y ⊗ₘ α.app X) ≫ @ExactPairing.evaluation D _ _ (G.obj X) (G.obj Y) (monoidalFunctor_exactPairing G X Y) = @ExactPairing.evaluation D _ _ (F.obj X) (F.obj Y) (monoidalFunctor_exactPairing F X Y) := by
-- proof
  apply TensorCategories.MonoidalFunctorProps.monoidalNatTrans_tensorHom_comp_eval F G α X Y

/--
[monoidalNatTrans_coev_comp_tensorHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorProps.lean)
-/
@[path]
private lemma monoidalNatTrans_coev_comp_tensorHom_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {D : Type u₂}
  [Category.{v₂} D]
  [MonoidalCategory D]
  {F G : C ⥤ D}
  [F.Monoidal]
  [G.Monoidal]
  {α : F ⟶ G}
  [α.IsMonoidal]
  {X Y : C}
  [ExactPairing X Y] :
-- imply
  @ExactPairing.coevaluation D _ _ (F.obj X) (F.obj Y) (monoidalFunctor_exactPairing F X Y) ≫ (α.app X ⊗ₘ α.app Y) = @ExactPairing.coevaluation D _ _ (G.obj X) (G.obj Y) (monoidalFunctor_exactPairing G X Y) := by
-- proof
  apply TensorCategories.MonoidalFunctorProps.monoidalNatTrans_coev_comp_tensorHom F G α X Y


-- created on 2026-10-23
