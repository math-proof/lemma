/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Tactic.Group
public import Instance.v1.Atlas.TensorCategories.code.GradedVec
public section

set_option maxHeartbeats 800000

open CategoryTheory

universe u v


/-- A normalised 3-cocycle: a `GroupCocycle3` satisfying
`ω(g, 1, h) = 1` for all `g, h ∈ G`. -/
structure NormalizedGroupCocycle3 (G : Type u) [Monoid G] (A : Type v) [CommMonoid A]
    extends GroupCocycle3 G A where
  normalized : ∀ g h : G, toFun g 1 h = 1

