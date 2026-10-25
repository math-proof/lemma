/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalization.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part3


namespace StatMech.Universality

open Complex HexWalk


namespace HexFiniteRegion

noncomputable def directedStartIncidence_of_returningUnique
    (R : HexFiniteRegion) (h0 : ℤ)
    (hunique : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = []) :
    R.DirectedStartIncidence h0 where
  dregion := fun m h => R.inRegion m ∧
    (m = R.start → halfStep h = halfStep h0)
  project := by
    intro m h hm
    exact hm.1
  walksInDirectedRegion := by
    intro ts hlegal hstay p hp
    obtain ⟨s, hs, rfl⟩ :=
      hexStripDirMids_mem_prefix_state R.start h0 ts p hp
    have hlegalS := hexStart_isLegalSAW_of_prefix R.start h0 hs hlegal
    have hstayS := hexStart_staysIn_of_prefix R.inRegion R.start h0 hs hstay
    refine ⟨?_, ?_⟩
    · have hm : (ofTurns R.start h0 s).endMid ∈
          (ofTurns R.start h0 s).mids := by
        unfold HexWalk.endMid
        exact List.getLast_mem _
      rw [hexInfra_endMid_eq_midAccum] at hm
      exact hstayS _ hm
    · intro hm
      have hend : (ofTurns R.start h0 s).EndsAt R.start := by
        rw [HexWalk.EndsAt, hexInfra_endMid_eq_midAccum]
        exact hm
      have hs0 := hunique s ⟨hlegalS, hstayS, hend⟩
      subst s
      rfl
  start_exact := by
    intro h hh
    exact hh.2 rfl


end HexFiniteRegion
end StatMech.Universality
