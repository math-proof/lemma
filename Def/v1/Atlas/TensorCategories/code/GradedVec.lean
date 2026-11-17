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
public import Structure.v1.Atlas.TensorCategories.code.GradedVec.Part2

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory

universe u v


/-- The trivial 3-cocycle, constantly equal to `1`. -/
def GroupCocycle3.trivial (G : Type u) [Monoid G] (A : Type v) [CommMonoid A] :
    GroupCocycle3 G A where
  toFun _ _ _ := 1
  cocycle_cond _ _ _ _ := by simp

/-- The trivial normalised 3-cocycle, constantly equal to `1`. -/
def NormalizedGroupCocycle3.trivial (G : Type u) [Monoid G] (A : Type v) [CommMonoid A] :
    NormalizedGroupCocycle3 G A where
  toGroupCocycle3 := GroupCocycle3.trivial G A
  normalized _ _ := rfl

