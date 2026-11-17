/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.SimpleRing.Field
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.RingTheory.Idempotents
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u w


noncomputable section

namespace TensorCategories

section EndUnitComm

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The monoid `End(𝟙_ C)` of endomorphisms of the unit object of a monoidal category is
commutative, packaged as a `CommMonoid` instance (Proposition 1.2.7). -/
instance endUnit_commMonoid : CommMonoid (End (𝟙_ C)) where
  mul_comm f g := by
    show g ≫ f = f ≫ g
    exact (endUnit_comm f g).symm

end EndUnitComm

section EndUnitCommRing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

/-- In a preadditive monoidal category, the endomorphism ring of the unit object is
commutative; this upgrades the ring structure on `End(𝟙_ C)` to a `CommRing`. -/
instance endUnit_commRing : CommRing (End (𝟙_ C)) :=
  { (inferInstance : Ring (End (𝟙_ C))) with
    mul_comm := fun f g => by
      show g ≫ f = f ≫ g
      exact (endUnit_comm f g).symm }

end EndUnitCommRing
end TensorCategories
end
