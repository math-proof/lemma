/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Mathlib.GroupTheory.GroupAction.Basic
import Theorem.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section Cohomology

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- A 2-cochain is a 2-cocycle if its coboundary `d²μ` vanishes identically. -/
def IsCocycle2 (μ : Cochain2 G A) : Prop :=
  ∀ g h l : G, d2 G A μ g h l = 1

/-- A 2-cochain is a 2-coboundary if it equals `d¹η` for some 1-cochain `η`. -/
def IsCoboundary2 (μ : Cochain2 G A) : Prop :=
  ∃ η : Cochain1 G A, ∀ g h, μ g h = d1 G A η g h

/-- A 3-cochain is a 3-cocycle if its coboundary `d³ω` vanishes identically. -/
def IsCocycle3 (ω : Cochain3' G A) : Prop :=
  ∀ g₁ g₂ g₃ g₄ : G, d3 G A ω g₁ g₂ g₃ g₄ = 1

/-- A 3-cochain is a 3-coboundary if it equals `d²μ` for some 2-cochain `μ`. -/
def IsCoboundary3 (ω : Cochain3' G A) : Prop :=
  ∃ μ : Cochain2 G A, ∀ g h l, ω g h l = d2 G A μ g h l

end Cohomology
