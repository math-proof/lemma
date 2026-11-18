/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.PivotalSpherical

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section Semisimple

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

def IsSemisimpleObject (X : C) : Prop :=
  ∃ (n : ℕ) (f : Fin n → C) (_ : HasBiproduct f),
    (∀ i, Simple (f i)) ∧ Nonempty (X ≅ @biproduct _ _ _ _ f ‹HasBiproduct f›)

end Semisimple
end CategoryTheory
end
