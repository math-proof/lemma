/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part4
public import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Simple
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.RingTheory.Coalgebra.Hom
public import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part5
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
public inductive IsInTensorClosure (P : C → Prop) : C → Prop where
  | of_base {X : C} (hX : P X) : IsInTensorClosure P X
  | of_unit : IsInTensorClosure P (𝟙_ C)
  | of_tensor {X Y : C} (hX : IsInTensorClosure P X) (hY : IsInTensorClosure P Y) :
      IsInTensorClosure P (X ⊗ Y)
  | of_directSum {X Y : C} (hX : IsInTensorClosure P X) (hY : IsInTensorClosure P Y) :
      IsInTensorClosure P (X ⊞ Y)

end TensorGenerated
end Prop_1_29_4
end Submodule
