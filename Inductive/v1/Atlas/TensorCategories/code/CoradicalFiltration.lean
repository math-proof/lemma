/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.CoalgebraBialgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Simple
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.RingTheory.Coalgebra.Hom
import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part5
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra

universe u v

variable {R : Type u} {C : Type v}
variable [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]


namespace Submodule

section Prop_1_29_4

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

variable {𝒞 : Type*} [CategoryTheory.Category 𝒞] [CategoryTheory.Abelian 𝒞]
    [CategoryTheory.HasExt 𝒞]

section TensorGenerated

universe v_tg u_tg

variable {C : Type u_tg} [Category.{v_tg} C]

variable [MonoidalCategory C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- The tensor-and-biproduct closure of a class `P` of objects: smallest class containing
`P`, the unit object, and closed under tensor product and direct sum. -/
inductive IsInTensorClosure (P : C → Prop) : C → Prop where
  | of_base {X : C} (hX : P X) : IsInTensorClosure P X
  | of_unit : IsInTensorClosure P (𝟙_ C)
  | of_tensor {X Y : C} (hX : IsInTensorClosure P X) (hY : IsInTensorClosure P Y) :
      IsInTensorClosure P (X ⊗ Y)
  | of_directSum {X Y : C} (hX : IsInTensorClosure P X) (hY : IsInTensorClosure P Y) :
      IsInTensorClosure P (X ⊞ Y)

end TensorGenerated
end Prop_1_29_4
end Submodule
