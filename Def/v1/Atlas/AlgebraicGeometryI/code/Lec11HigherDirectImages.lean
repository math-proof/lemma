/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec11HigherDirectImages.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Topology.NoetherianSpace

@[expose] public section

universe u v w

open CategoryTheory Limits TopologicalSpace Opposite


/-- The sections functor `Γ(U, –) : Sheaf C X → C` sending a sheaf to its sections on
a fixed open `U`, constructed by forgetting to a presheaf and evaluating at `U`. -/
noncomputable def TopCat.Sheaf.sectionsFunctor
    (C : Type u) [Category.{v} C] {X : TopCat.{w}} (U : Opens X) :
    TopCat.Sheaf C X ⥤ C :=
  TopCat.Sheaf.forget C X ⋙ (evaluation (Opens X)ᵒᵖ C).obj (op U)


