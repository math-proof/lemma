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
import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part7
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

section CategoricalConjecture

universe w_cc v_cc u_cc

variable (k : Type w_cc) [Field k] [CharZero k]

variable (C : Type u_cc) [Category.{v_cc} C] [FiniteTensorCategory k C]

/-- Conjecture 1.32.4 (EGNO): the categorical Andruskiewitsch-Schneider conjecture about
cocommutative Hopf algebras over algebraically closed fields of characteristic zero. -/
abbrev Conjecture_1_32_4 := @AndruskiewitschSchneiderCategorical

end CategoricalConjecture
end Prop_1_29_4
end Submodule
