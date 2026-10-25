/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Theorem.v1.Atlas.TensorCategories.code.MonoidalFunctorProps.Part3
set_option maxHeartbeats 800000


namespace TensorCategories.MonoidalFunctorProps

open CategoryTheory MonoidalCategory Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

section Exercise_1_10_15

open Category

/-- Part of EGNO Exercise 1.10.15: a monoidal natural transformation between strong
monoidal functors has invertible component at any right-dualizable object. -/
noncomputable instance monoidalNatTrans_isIso_of_hasRightDual
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X : C) [HasRightDual X] : IsIso (α.app X) := by
  refine ⟨⟨monoidalNatTrans_inv F G α X, ?_, ?_⟩⟩
  ·
    simp only [monoidalNatTrans_inv]

    rw [leftUnitor_inv_naturality_assoc]

    slice_lhs 2 3 => rw [whisker_exchange]
    try simp only [assoc]

    slice_lhs 3 4 => rw [associator_naturality_right]
    try simp only [assoc]

    slice_lhs 4 5 => rw [← MonoidalCategory.whiskerLeft_comp]

    rw [← tensorHom_def']

    slice_lhs 4 5 => rw [← MonoidalCategory.whiskerLeft_comp]

    rw [monoidalNatTrans_tensorHom_comp_eval]

    slice_lhs 2 4 => rw [ExactPairing.evaluation_coevaluation]
    simp
  ·
    simp only [monoidalNatTrans_inv, assoc]

    slice_lhs 6 7 => rw [← rightUnitor_naturality]
    try simp only [assoc]

    slice_lhs 5 6 => rw [whisker_exchange]
    try simp only [assoc]

    slice_lhs 4 5 => rw [whisker_exchange]
    try simp only [assoc]

    slice_lhs 3 4 => rw [← associator_naturality_left]
    try simp only [assoc]

    slice_lhs 2 3 => rw [← comp_whiskerRight]
    try simp only [assoc]

    rw [show (η_ (F.obj X) (F.obj Xᘁ) ≫ α.app X ▷ F.obj Xᘁ) ▷ G.obj X =
      η_ (F.obj X) (F.obj Xᘁ) ▷ G.obj X ≫ (α.app X ▷ F.obj Xᘁ) ▷ G.obj X
      from comp_whiskerRight _ _ _]
    try simp only [assoc]

    slice_lhs 3 4 => rw [associator_naturality_left]
    try simp only [assoc]

    slice_lhs 4 5 => rw [← whisker_exchange]
    try simp only [assoc]

    slice_lhs 3 4 => rw [← associator_naturality_middle]
    try simp only [assoc]

    slice_lhs 4 5 => rw [← associator_naturality_left]
    try simp only [assoc]

    slice_lhs 3 4 => rw [← comp_whiskerRight]
    try simp only [assoc]

    rw [← tensorHom_def']

    slice_lhs 2 3 => rw [← comp_whiskerRight]

    rw [monoidalNatTrans_coev_comp_tensorHom]

    slice_lhs 2 4 => rw [ExactPairing.evaluation_coevaluation]
    simp

/-- EGNO Exercise 1.10.15 (rigid case): when both `C` and `D` are right-rigid, every
monoidal natural transformation between strong monoidal functors is a natural
isomorphism. -/
noncomputable instance monoidalNatTrans_isIso_of_rigid
    [RightRigidCategory C] [RightRigidCategory D]
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X : C) : IsIso (α.app X) :=
  monoidalNatTrans_isIso_of_hasRightDual F G α X

end Exercise_1_10_15
end TensorCategories.MonoidalFunctorProps
