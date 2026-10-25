/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InvertibleObjects.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Theorem.v1.Atlas.TensorCategories.code.InvertibleObjects
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [RigidCategory C]

section LeftDualIsoRightDual

variable (X : C) [HasRightDual X] [IsIso (ε_ X (Xᘁ))] [IsIso (η_ X (Xᘁ))]

/-- When the evaluation and coevaluation of `X` and `Xᘁ` are both isomorphisms, `Xᘁ`
together with `X` forms an exact pairing using their inverses. -/
@[reducible]
noncomputable def exactPairingDualObj : ExactPairing (Xᘁ) X where
  coevaluation' := inv (ε_ X Xᘁ)
  evaluation' := inv (η_ X Xᘁ)
  coevaluation_evaluation' := zigzag_inv_coeval_eval X
  evaluation_coevaluation' := zigzag_inv_eval_coeval X

/-- For an invertible object `X` in a rigid category, the left dual is canonically
isomorphic to the right dual. -/
noncomputable def leftDualIsoRightDual_of_invertible : HasLeftDual.leftDual X ≅ Xᘁ :=
  leftDualIso (inferInstance : ExactPairing (HasLeftDual.leftDual X) X) (exactPairingDualObj X)

end LeftDualIsoRightDual

/-- Proposition 1.11.3: for an invertible object `X` in a rigid category, (i) the left
dual is isomorphic to the right dual, (ii) the tensor inverse is invertible, and (iii)
the tensor product of invertibles is invertible. -/
noncomputable def Proposition_1_11_3
    (X : C) [IsIso (ε_ X (Xᘁ))] [IsIso (η_ X (Xᘁ))] :

    (HasLeftDual.leftDual X ≅ Xᘁ) ×

    (∀ [IsInvertibleObject X], IsInvertibleObject (IsInvertibleObject.tensorInverse X)) ×

    (∀ (Y : C) [IsInvertibleObject X] [IsInvertibleObject Y],
      IsInvertibleObject (X ⊗ Y)) :=
  ⟨leftDualIsoRightDual_of_invertible X,
   IsInvertibleObject.inverseInvertible X,
   fun Y => tensor_invertible X Y⟩

section InvertibleSubcategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The object property of being invertible, packaged as an `ObjectProperty C` for use
when forming the monoidal subcategory of invertible objects. -/
def IsInvertibleObjectProp : ObjectProperty C := fun X => Nonempty (IsInvertibleObject X)

end InvertibleSubcategory
end CategoryTheory
