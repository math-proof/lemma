/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterHomomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof
import Mathlib.GroupTheory.Coxeter.Basic
open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The family of reflections $\sigma_s \in GL(\mathbb{R}^B)$ satisfies the
Coxeter braid relations, so it satisfies the lifting hypothesis for $M$. -/
theorem sigmaLinearEquiv_isLiftable (M : CoxeterMatrix B) :
    M.IsLiftable (fun s => sigmaLinearEquiv M s) := by
  intro s t


  ext v : 1

  simp only [LinearEquiv.coe_one, id_eq, LinearEquiv.coe_pow]

  have hcoe : ⇑(sigmaLinearEquiv M s * sigmaLinearEquiv M t) =
      fun w => sigma M s (sigma M t w) := rfl
  rw [hcoe]

  by_cases hm : M.M s t = 0
  · simp [hm]
  · exact (braidRelationHyp M).braid_power_eq_one s t hm v


end CoxeterGroup
