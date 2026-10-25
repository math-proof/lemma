/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusProof
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part3
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part4
import Class.v1.Atlas.Buildings.code.AffineCoxeter.AffineCriterion.Part2
set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Default constructor: chamber-chasing follows from the local finiteness of nonposRoots and the
characterization of the Tits cone in terms of $\nu$-finite points. -/
theorem chamberChasingProperty_instance
    {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) [RootSystemData M] :
    ChamberChasingProperty M := by
  constructor
  intro v₀ hv₀_pos hv₀_rad _hAff x hx

  have hx_ne : x ≠ 0 := by
    intro hx_eq
    subst hx_eq
    simp only [affineHyperplane, Set.mem_setOf_eq, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at hx
    norm_num at hx


  have hx_sum : ∑ s, v₀ s * x s = 1 := by
    simp only [affineHyperplane, Set.mem_setOf_eq] at hx; exact hx
  have hnu : nuFiniteAt (RootSystemData.Φpos (M := M)) x :=
    RootSystemData.nonposRoots_finite_on_hyperplane v₀ hv₀_pos hv₀_rad x hx_sum

  have hx_cone := nuFinite_mem_titsCone M x hx_ne hnu

  exact ⟨x, x, 0, hx_cone, hx_cone, le_refl 0, zero_le_one, fun s => by ring⟩

