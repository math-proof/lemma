/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.CoalgebraBialgebra
public import Theorem.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
public import Theorem.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
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
public import Structure.v1.Atlas.TensorCategories.code.CoradicalFiltration

@[expose] public section

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

/-- The `n`-th associated graded piece of a filtration `F`: `F n / F (n-1)`, with the
convention that for `n = 0` the bottom level is `⊥`. -/
noncomputable def associatedGraded {R : Type*} {H : Type*}
    [CommRing R] [AddCommGroup H] [Module R H]
    (F : ℕ → Submodule R H) (n : ℕ) : Type _ :=
  ↥(F n) ⧸ (Submodule.comap (F n).subtype (if n = 0 then ⊥ else F (n - 1)))

/-- The coradical filtration of a pointed Hopf algebra over a field is a Hopf-algebra
filtration (Corollary 1.31.5 in EGNO). -/
def IsSemisimpleObject (C : Type*) [Category C] [HasZeroMorphisms C] (X : C) : Prop :=
  ∃ (n : ℕ) (f : Fin n → C) (_ : HasBiproduct f),
    (∀ i, Simple (f i)) ∧ Nonempty (X ≅ @biproduct _ _ _ _ f ‹HasBiproduct f›)

end Prop_1_29_4
end Submodule
