module
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Theorem.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
public import Theorem.Category.Atlas.v1.TensorCategories.code.HigherDerivation
public import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity
public import Instance.v1.Atlas.TensorCategories.code.HigherDerivation
set_option maxHeartbeats 800000
open CategoryTheory MonoidalCategory Category Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ext1UnitVanishing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe v u w


noncomputable section

namespace TensorCategories

section Ext1Def

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The predicate `Ext¹(X, Y) = 0` expressed as: every short exact sequence
`0 → Y → V → X → 0` splits. -/
def Ext1Vanishes (X Y : C) : Prop :=
  ∀ (V : C) (f : Y ⟶ V) (g : V ⟶ X) (hfg : f ≫ g = 0),
    (ShortComplex.mk f g hfg).ShortExact → Nonempty (ShortComplex.mk f g hfg).Splitting

end Ext1Def
end TensorCategories
end
