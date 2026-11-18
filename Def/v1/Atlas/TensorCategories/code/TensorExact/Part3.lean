/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Abelian.Basic
public import Instance.v1.Atlas.TensorCategories.code.TensorExact.Part2

@[expose] public section

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Opposite

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

section ExactFunctors

/-- The right dualization functor `Cᵒᵖ ⥤ C` is exact, packaged as an `exactFunctor`. -/
noncomputable def rightDualizationFunctor_exact :
    exactFunctor Cᵒᵖ C (rightDualizationFunctor (C := C)) :=
  ⟨rightDualizationFunctor_preservesFiniteLimits,
   rightDualizationFunctor_preservesFiniteColimits⟩

/-- The left dualization functor `Cᵒᵖ ⥤ C` is exact, packaged as an `exactFunctor`. -/
noncomputable def leftDualizationFunctor_exact :
    exactFunctor Cᵒᵖ C (leftDualizationFunctor (C := C)) :=
  ⟨leftDualizationFunctor_preservesFiniteLimits,
   leftDualizationFunctor_preservesFiniteColimits⟩

end ExactFunctors
end CategoryTheory
