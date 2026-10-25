/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation.Part2
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- $\sigma_s$ as a linear automorphism of $\mathbb{R}^B$, built from the involution
property. -/
noncomputable def sigmaLinearEquiv (M : CoxeterMatrix B) (s : B) : (B → ℝ) ≃ₗ[ℝ] (B → ℝ) :=
  LinearEquiv.ofInvolutive (sigmaLinearMap M s) (sigma_involution M s)

end CoxeterGroup
