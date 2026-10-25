/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part5
open Finset


namespace StatMech.Sharpness

theorem shbK4H_masses_at_two_thirds :
    shbK4DirectFiberMass shbK4H (2 / 3) = 2 / 3 ∧
      shbK4VacuumMass shbK4H (2 / 3) = 145 / 81 := by
  decide +kernel


theorem shbK4G_masses_at_two_thirds :
    shbK4DirectFiberMass shbK4G (2 / 3) = 86 / 81 ∧
      shbK4VacuumMass shbK4G (2 / 3) = 25 / 9 := by
  decide +kernel


theorem shbK4_rhos_at_two_thirds :
    shbK4DirectRho shbK4H (2 / 3) = 54 / 145 ∧
      shbK4DirectRho shbK4G (2 / 3) = 86 / 225 := by
  constructor
  · unfold shbK4DirectRho
    rw [shbK4H_masses_at_two_thirds.1, shbK4H_masses_at_two_thirds.2]
    norm_num
  · unfold shbK4DirectRho
    rw [shbK4G_masses_at_two_thirds.1, shbK4G_masses_at_two_thirds.2]
    norm_num


theorem shb_supportLex_edgeDomain_P3_counterexample :
    shbK4DirectRho shbK4H (2 / 3) < shbK4DirectRho shbK4G (2 / 3) := by
  rw [shbK4_rhos_at_two_thirds.1, shbK4_rhos_at_two_thirds.2]
  norm_num


theorem shbK4H_ssubset_shbK4G : shbK4H ⊂ shbK4G := by
  decide +kernel

end StatMech.Sharpness
