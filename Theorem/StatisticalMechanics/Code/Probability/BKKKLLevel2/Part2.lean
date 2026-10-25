/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.BKKKLTruncation.Part2
import Def.StatisticalMechanics.Code.Probability.BKKKLLevel2
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bkt2_lowDegreeMaster_of_levelGe2 {q : ℝ} (H : bkt2_levelGe2MasterResidue q) :
    bkt_lowDegreeMasterResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  obtain ⟨k, hk1, hk⟩ := H p hp hp1 φ u hu0 hu1
  refine ⟨k, ?_⟩
  
  set B : ℝ := (4 * (ptn_sigma p) ^ 2)
      * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        - (1 - u) ^ k)
      * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hB
  
  exact (lib_residue_iff_levelGe2 φ hk1 (B := B)).mpr hk


theorem bkt2_master_of_levelGe2 {q : ℝ} (H : bkt2_levelGe2MasterResidue q) :
    pro_PBiasedMaster q :=
  bkt_master_of_residue (bkt2_lowDegreeMaster_of_levelGe2 H)


end StatMech.Probability
