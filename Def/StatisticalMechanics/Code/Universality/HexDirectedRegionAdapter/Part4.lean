/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter.Part3


namespace StatMech.Universality

open Complex HexWalk


noncomputable def hexStrip_straightSide_distinctMidpoint
    (dregion : ℂ → ℤ → Prop) (inRegion : ℂ → Prop)
    (a : ℂ) (h0 : ℤ) (z : ℂ) (Hd : ℤ)
    (huniq : ∀ h : ℤ,
      hexStripInteriorDistinctMidpoint dregion (z + halfStep h) →
        halfStep h = halfStep (Hd + 3))
    (hbridge : ∀ ts : List ℤ,
      (ofTurns a h0 ts).IsLegalSAW
        ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z →
      hexStripStaysInDir dregion a h0 ts) :
    HexStraightSide inRegion
      (hexStripInteriorDistinctMidpoint dregion) a h0 z where
  H := Hd
  uniqueInterior := huniq
  interiorVertices := by
    intro ts hadm v hv hvne
    have hzm : hexInfra_midAccum a h0 ts = z := by
      rw [← hexInfra_endMid_eq_midAccum]
      exact hadm.2.2
    refine hexStrip_interiorVertices_distinctMidpoint_core
      dregion a h0 ts hadm.1 (hbridge ts hadm) v hv ?_
    rw [hzm]
    exact hvne

namespace HexFiniteRegion


noncomputable def directedStartIncidence_closed
    (R : HexFiniteRegion) (h0 : ℤ) : R.DirectedStartIncidence h0 :=
  R.directedStartIncidence_of_returningUnique h0 (R.returningSAW_eq_nil h0)


noncomputable def directedStartIncidence_of_distinctMidpointStripStartGeometry
    (R : HexFiniteRegion) (h0 : ℤ) (dregion : ℂ → ℤ → Prop)
    (huniq : ∀ h : ℤ,
      hexStripInteriorDistinctMidpoint dregion (R.start + halfStep h) →
        halfStep h = halfStep h0)
    (hlaunch : dregion R.start h0) :
    R.DirectedStartIncidence h0 := by
  let S : HexStraightSide R.inRegion
      (hexStripInteriorDistinctMidpoint dregion) R.start h0 R.start :=
    hexStrip_straightSide_distinctMidpoint
      dregion R.inRegion R.start h0 R.start (h0 + 3)
      (by
        intro h hint
        calc
          halfStep h = halfStep h0 := huniq h hint
          _ = halfStep ((h0 + 3) + 3) := by
            rw [show ((h0 + 3) + 3 : ℤ) = h0 + 6 by ring,
              hexStrip_halfStep_add6])
      (by
        intro ts hts
        exact hexReturning_staysInDir_of_launch
          dregion R.start h0 hlaunch ts hts.1 hts.2.2)
  exact R.directedStartIncidence_of_straightStart_reverse h0
    (hexStripInteriorDistinctMidpoint dregion) S (by
      change halfStep (h0 + 3) = -halfStep h0
      exact hexW1Exit_halfStep_add_three h0)

end HexFiniteRegion
end StatMech.Universality
