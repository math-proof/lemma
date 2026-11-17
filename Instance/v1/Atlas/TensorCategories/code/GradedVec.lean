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
public import Structure.v1.Atlas.TensorCategories.code.GradedVec

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory

universe u v


/-- Coerce a `GroupCocycle3` to its underlying function `G → G → G → A`. -/
instance {G : Type u} [Monoid G] {A : Type v} [CommMonoid A] :
    CoeFun (GroupCocycle3 G A) (fun _ => G → G → G → A) :=
  ⟨GroupCocycle3.toFun⟩

