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
import Abbrev.v1.Atlas.TensorCategories.code.CoradicalFiltration
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra

universe u v

variable {R : Type u} {C : Type v}
variable [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]


namespace Submodule

/-- A coalgebra `C` is pointed if every simple subcoalgebra of `C` is one-dimensional, i.e.
spanned by a grouplike element. -/
def IsPointedCoalgebra : Prop :=
  ∀ S : Submodule R C, S.IsSimpleCoalgebra →
    ∃ g : C, S = Submodule.span R {g}


/-- The submodule `∑_{i+j=n} C_i ⊗ C_j ⊆ C ⊗ C` used to formulate the comultiplication
compatibility of the coradical filtration. -/
noncomputable def filtrationTensorSum (n : ℕ) : Submodule R (C ⊗[R] C) :=
  ⨆ (i : Fin (n + 1)),
    Submodule.map₂ (TensorProduct.mk R C C)
      (coradicalFiltration i.val) (coradicalFiltration (n - i.val))

/-- The right slice operator on `C` associated to a functional `f : C → R`: applies
`comul` then contracts the right factor through `f`. -/
noncomputable def coalgebraRightSlice (f : C →ₗ[R] R) : C →ₗ[R] C :=
  (TensorProduct.rid R C).toLinearMap.comp
    ((LinearMap.lTensor C f).comp (Coalgebra.comul (R := R)))

/-- The left slice operator on `C` associated to a functional `f : C → R`: applies
`comul` then contracts the left factor through `f`. -/
noncomputable def coalgebraLeftSlice (f : C →ₗ[R] R) : C →ₗ[R] C :=
  (TensorProduct.lid R C).toLinearMap.comp
    ((LinearMap.rTensor C f).comp (Coalgebra.comul (R := R)))

/-- Dual reduction step: if a coalgebra homomorphism `f` is injective on `C_1`, then it is
injective on each level `C_n` of the coradical filtration, via algebra-side surjectivity. -/
def Ext1VanishesForSimples (𝒞 : Type*) [CategoryTheory.Category 𝒞]
    [CategoryTheory.Abelian 𝒞] [CategoryTheory.HasExt 𝒞]
    [CategoryTheory.Limits.HasZeroMorphisms 𝒞] : Prop :=
  ∀ (X Y : 𝒞) [CategoryTheory.Simple X] [CategoryTheory.Simple Y],
    Subsingleton (CategoryTheory.Abelian.Ext X Y 1)

/-- An abelian category is semisimple if `Ext^1` vanishes between all pairs of objects. -/
def IsSemisimpleCat (𝒞 : Type*) [CategoryTheory.Category 𝒞]
    [CategoryTheory.Abelian 𝒞] [CategoryTheory.HasExt 𝒞] : Prop :=
  ∀ (X Y : 𝒞), Subsingleton (CategoryTheory.Abelian.Ext X Y 1)

end Submodule
