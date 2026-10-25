/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripMassLimits


namespace StatMech.Universality

open HexWalk Filter Topology

noncomputable section

theorem hexCSClassWalkMass_eq_predicateMass
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) :
    hexCSClassWalkMass T L hT cls =
      hexCSPredicateMass (HexCSClassWalk T L hT cls) := by
  rfl

theorem hexCSA_eq_sideWalkMass (T L : ℕ) (hT : 0 < T) :
    hexCSA T L hT = hexCSPredicateMass (HexCSSideWalk T L hT) := by
  rw [hexCSA_eq_classWalkMass, hexCSClassWalkMass_eq_predicateMass]
  unfold hexCSPredicateMass
  apply tsum_congr
  intro ts
  classical
  unfold hexCSPredicateWeight
  rw [if_congr (hexCSClassWalk_side_iff T L hT ts) rfl rfl]

theorem hexCSE_eq_slantWalkMass (T L : ℕ) (hT : 0 < T) :
    hexCSE T L hT = hexCSPredicateMass (HexCSSlantWalk T L hT) := by
  rw [hexCSE_eq_classWalkMass, hexCSClassWalkMass_eq_predicateMass]
  unfold hexCSPredicateMass
  apply tsum_congr
  intro ts
  classical
  unfold hexCSPredicateWeight
  rw [if_congr (hexCSClassWalk_slant_iff T L hT ts) rfl rfl]

theorem hexCSB_eq_topWalkMass (T L : ℕ) (hT : 0 < T) :
    hexCSB T L hT = hexCSPredicateMass (HexCSTopWalk T L hT) := by
  rw [hexCSB_eq_classWalkMass, hexCSClassWalkMass_eq_predicateMass]
  unfold hexCSPredicateMass
  apply tsum_congr
  intro ts
  classical
  unfold hexCSPredicateWeight
  rw [if_congr (hexCSClassWalk_top_iff T L hT ts) rfl rfl]

end
end StatMech.Universality
