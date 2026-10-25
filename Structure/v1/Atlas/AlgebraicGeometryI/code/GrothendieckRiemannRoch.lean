/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckRiemannRoch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


noncomputable section

namespace GRR

/-- Chow-ring data: a commutative `ℚ`-algebra packaging the Chow ring `A^*(X) ⊗ ℚ` used in
the Grothendieck-Riemann-Roch statement. -/
structure ChowRingData where
  Ring : Type
  instCommRing : CommRing Ring
  instAlgebra : Algebra ℚ Ring

attribute [instance] ChowRingData.instCommRing ChowRingData.instAlgebra

/-- Bundle of data needed for Grothendieck-Riemann-Roch along a proper morphism `f : X → Y`:
Chow rings of `X` and `Y`, K-theory groups, derived/Chow pushforwards, Chern characters, and the
relative Todd class. -/
structure ProperMorphismGRR where
  chowX : ChowRingData
  chowY : ChowRingData
  K0X : Type
  instK0X : AddCommGroup K0X
  K0Y : Type
  instK0Y : AddCommGroup K0Y
  derived_pushforward : K0X →+ K0Y
  chow_pushforward : chowX.Ring →ₗ[ℚ] chowY.Ring
  chern_character_X : K0X →+ chowX.Ring
  chern_character_Y : K0Y →+ chowY.Ring
  todd_class_relative : chowX.Ring

attribute [instance] ProperMorphismGRR.instK0X

attribute [instance] ProperMorphismGRR.instK0Y

/-- Grothendieck-Riemann-Roch: for a proper morphism `f : X → Y`,
`ch(f_! α) = f_*(ch(α) · td(T_f))` in the Chow ring of `Y`. -/
structure HRRData where
  chowX : ChowRingData
  K0X : Type
  instK0X : AddCommGroup K0X
  euler_char : K0X →+ ℤ
  degree : chowX.Ring →ₗ[ℚ] ℚ
  chern_character : K0X →+ chowX.Ring
  todd_class : chowX.Ring
  hrr_formula : ∀ α : K0X,
    (euler_char α : ℚ) = degree (chern_character α * todd_class)

end GRR
end
