/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.RingTheory.Idempotents
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact
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
