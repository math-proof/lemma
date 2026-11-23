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
public import Instance.v1.Atlas.TensorCategories.code.GradedVec.Part4
set_option maxHeartbeats 800000

open CategoryTheory

public section

universe u v


example (G : Type*) (C : Type*) : GradedObject G C = (G → C) := rfl

