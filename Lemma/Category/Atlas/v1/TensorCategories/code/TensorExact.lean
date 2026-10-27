import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.TensorExact.Part3
open CategoryTheory MonoidalCategory Limits Opposite


namespace CategoryTheory

/--
[tensor_biexact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean)
-/
@[path]
lemma tensor_biexact
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {X : C} :
-- imply
  exactFunctor C C (tensorLeft X) ∧ exactFunctor C C (tensorRight X) :=
-- proof
  ⟨tensorLeft_exact X, tensorRight_exact X⟩

end CategoryTheory

namespace CategoryTheory

/--
[proposition_1_13_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean)
-/
@[path]
lemma proposition_1_13_1
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {X : C} :
-- imply
  exactFunctor C C (tensorLeft X) ∧ exactFunctor C C (tensorRight X) :=
-- proof
  tensor_biexact X

end CategoryTheory

namespace CategoryTheory

/--
[dualization_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean)
-/
@[path]
lemma dualization_exact
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C] :
-- imply
  exactFunctor Cᵒᵖ C (rightDualizationFunctor (C := C)) ∧ exactFunctor Cᵒᵖ C (leftDualizationFunctor (C := C)) :=
-- proof
  ⟨rightDualizationFunctor_exact, leftDualizationFunctor_exact⟩

end CategoryTheory

namespace CategoryTheory

/--
[prop_1_13_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean)
-/
@[path]
lemma prop_1_13_5
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C] :
-- imply
  exactFunctor Cᵒᵖ C (rightDualizationFunctor (C := C)) ∧ exactFunctor Cᵒᵖ C (leftDualizationFunctor (C := C)) :=
-- proof
  dualization_exact

end CategoryTheory

/--
[rightAdjointMateEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean)
-/
@[path]
private lemma rightAdjointMateEquiv_apply_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {X Y : C}
  {f : X ⟶ Y} :
-- imply
  rightAdjointMateEquiv X Y f = rightAdjointMate f := by
-- proof
  apply CategoryTheory.rightAdjointMateEquiv_apply X Y f

/--
[leftAdjointMateEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean)
-/
@[path]
private lemma leftAdjointMateEquiv_apply_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {X Y : C}
  {f : X ⟶ Y} :
-- imply
  leftAdjointMateEquiv X Y f = leftAdjointMate f := by
-- proof
  apply CategoryTheory.leftAdjointMateEquiv_apply X Y f


-- created on 2026-10-23
