/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidAbelianDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Def.v1.Atlas.TensorCategories.code.InvertibleObjects
public import Def.v1.Atlas.TensorCategories.code.InvertibleObjects.Part2

@[expose] public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory


/-- The tensor inverse of an invertible object is itself invertible. -/
noncomputable def invertibleObject_inverse_invertible {C : Type*} [Category C] [MonoidalCategory C]
    (X : C) [h : IsInvertibleObject X] : IsInvertibleObject h.tensorInverse :=
  IsInvertibleObject.inverseInvertible X

/-- For an invertible object X in a rigid monoidal category, the canonical left
and right duals are isomorphic. -/
noncomputable def invertibleObject_leftDual_iso_rightDual
    {C : Type*} [Category C] [MonoidalCategory C] [RigidCategory C]
    (X : C) [HasRightDual X] [IsIso (ε_ X (Xᘁ))] [IsIso (η_ X (Xᘁ))] :
    HasLeftDual.leftDual X ≅ Xᘁ :=
  leftDualIsoRightDual_of_invertible X

/-- The tensor product of two invertible objects in a rigid monoidal category is
again invertible. -/
noncomputable def invertibleObject_tensor
    {C : Type*} [Category C] [MonoidalCategory C] [RigidCategory C]
    (X Y : C) [hX : IsInvertibleObject X] [hY : IsInvertibleObject Y] :
    IsInvertibleObject (X ⊗ Y) :=
  tensor_invertible X Y
