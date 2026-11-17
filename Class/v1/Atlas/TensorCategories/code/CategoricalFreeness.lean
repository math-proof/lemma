module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CategoricalFreeness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Def.v1.Atlas.TensorCategories.code.CategoricalFreeness
public section

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w


namespace CategoryTheory

/-- Combinatorial data describing the simple/projective decomposition of a finite
multitensor category: a finite indexing type `I`, simple objects `simpleObj i`, projective
covers `projCover i`, multiplicities of `projCover` in arbitrary objects, and the
distinguished index for the unit object. -/
class FiniteMultitensorDecompData (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] where
  I : Type*
  [instFintype : Fintype I]
  [instDecEq : DecidableEq I]
  simpleObj : I → C
  projCover : I → C
  projDecompMult : C → I → ℕ
  unitIdx : I
  simpleObj_unitIdx : Nonempty (simpleObj unitIdx ≅ 𝟙_ C)

end CategoryTheory
