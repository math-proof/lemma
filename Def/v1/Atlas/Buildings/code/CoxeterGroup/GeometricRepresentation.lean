/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The geometric reflection $\sigma_s : \mathbb{R}^B \to \mathbb{R}^B$ associated to
$s \in S$, packaged as an $\mathbb{R}$-linear map. -/
noncomputable def sigmaLinearMap (M : CoxeterMatrix B) (s : B) : (B → ℝ) →ₗ[ℝ] (B → ℝ) where
  toFun := sigma M s
  map_add' := sigma_add M s
  map_smul' := sigma_smul M s

end CoxeterGroup
