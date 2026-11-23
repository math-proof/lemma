/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PivotalSpherical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Def.v1.Atlas.TensorCategories.code.PivotalSpherical.Part2
@[expose] public section

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory Category Limits

universe w v u


namespace TensorCategories

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

section PivotalSection

variable [PivotalCategory C]

/-- Alias for `pivotalDimension`: the left quantum dimension of `V`. -/
noncomputable abbrev leftQuantumDim (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalDimension C V

/-- Alias for `pivotalDimension`: the categorical dimension of `V`. -/
noncomputable abbrev categoricalDimension (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalDimension C V

end PivotalSection
end TensorCategories
