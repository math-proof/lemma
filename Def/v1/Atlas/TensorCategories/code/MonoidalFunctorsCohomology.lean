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
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section GroupCochains

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- A 1-cochain on the group `G` with values in the commutative group `A`: a function
`G → A`. -/
def Cochain1 := G → A

/-- A 2-cochain on the group `G` with values in the commutative group `A`: a function
`G × G → A`. -/
def Cochain2 := G → G → A

/-- A 3-cochain on the group `G` with values in the commutative group `A`: a function
`G × G × G → A`. -/
def Cochain3' := G → G → G → A

/-- A 4-cochain on the group `G` with values in the commutative group `A`: a function
`G⁴ → A`. -/
def Cochain4 := G → G → G → G → A

/-- The group coboundary `d¹η(g, h) = η(g) η(h) η(gh)⁻¹` sending a 1-cochain to a
2-cochain. -/
def d1 (η : Cochain1 G A) : Cochain2 G A :=
  fun g h => η g * η h * (η (g * h))⁻¹

/-- The group coboundary `d²μ(g, h, l) = μ(h,l) μ(g, hl) μ(gh, l)⁻¹ μ(g, h)⁻¹` sending a
2-cochain to a 3-cochain. -/
def d2 (μ : Cochain2 G A) : Cochain3' G A :=
  fun g h l => μ h l * μ g (h * l) * (μ (g * h) l)⁻¹ * (μ g h)⁻¹

/-- The group coboundary `d³ω` sending a 3-cochain to a 4-cochain. -/
def d3 (ω : Cochain3' G A) : Cochain4 G A :=
  fun g₁ g₂ g₃ g₄ =>
    ω g₂ g₃ g₄ * ω g₁ (g₂ * g₃) g₄ * ω g₁ g₂ g₃ *
    (ω g₁ g₂ (g₃ * g₄))⁻¹ * (ω (g₁ * g₂) g₃ g₄)⁻¹

end GroupCochains
