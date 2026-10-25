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
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part3


namespace StatMech.Universality

open Complex HexWalk


namespace HexFiniteRegion

theorem returningSAW_eq_nil_of_directedStartIncidence
    (R : HexFiniteRegion) (h0 : ℤ) (S : R.DirectedStartIncidence h0) :
    ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
  intro ts hts
  have hdir := S.walksInDirectedRegion ts hts.1 hts.2.1
  have hfinal : S.dregion
      (hexInfra_midAccum R.start h0 ts) (hexInfra_headAccum h0 ts) :=
    hdir _ (hexStripDirMids_final_mem R.start h0 ts)
  have hend : hexInfra_midAccum R.start h0 ts = R.start := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hts.2.2
  have hheading : halfStep (hexInfra_headAccum h0 ts) = halfStep h0 := by
    apply S.start_exact
    rwa [hend] at hfinal
  apply hexLegalSAW_eq_nil_of_lastVertex_eq_first R.start h0 ts hts.1
  rw [hend, hheading]


theorem hexStrip_singleRegion_legal_stays_eq_nil
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn (hexStrip_singleRegion a).inRegion) :
    ts = [] := by
  have hstayEq : (ofTurns a h0 ts).StaysIn (fun m => m = a) := by
    intro m hm
    have hm' := hstay m hm
    simpa [hexStrip_singleRegion, hexStrip_finiteRegion,
      HexFiniteRegion.inRegion] using hm'
  have hend : (ofTurns a h0 ts).EndsAt a := by
    rw [HexWalk.EndsAt]
    apply hstayEq
    unfold HexWalk.endMid
    exact List.getLast_mem _
  exact hexW1_singleton_admissible_nil a h0 ts ⟨hlegal, hstayEq, hend⟩


end HexFiniteRegion
end StatMech.Universality
