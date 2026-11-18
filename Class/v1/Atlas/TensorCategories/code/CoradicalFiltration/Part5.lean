module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Abbrev.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part4
public section
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

section ChevalleyProperty

universe v_cp u_cp

variable (C : Type u_cp) [Category.{v_cp} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A tensor category has the Chevalley property if the tensor product of any two
semisimple objects is semisimple. -/
class HasChevalleyProperty : Prop where
  tensor_semisimple : ∀ (X Y : C),
    IsSemisimpleObject C X → IsSemisimpleObject C Y → IsSemisimpleObject C (X ⊗ Y)

end ChevalleyProperty
end Prop_1_29_4
end Submodule
