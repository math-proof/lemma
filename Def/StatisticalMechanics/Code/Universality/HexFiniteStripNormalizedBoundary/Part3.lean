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
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part4


namespace StatMech.Universality

open Complex HexWalk


namespace HexFiniteRegion

noncomputable def directedStartIncidence_of_straightStart_reverse
    (R : HexFiniteRegion) (h0 : ℤ) (interior : ℂ → Prop)
    (S : HexStraightSide R.inRegion interior R.start h0 R.start)
    (hreverse : halfStep S.H = -halfStep h0) :
    R.DirectedStartIncidence h0 :=
  R.directedStartIncidence_of_returningUnique h0
    (R.returningSAW_eq_nil_of_straightStart_reverse h0 interior S hreverse)


noncomputable def directedStartIncidence_of_stripStartGeometry
    (R : HexFiniteRegion) (h0 : ℤ) (dregion : ℂ → ℤ → Prop)
    (huniq : ∀ h : ℤ,
      hexStripInterior dregion (R.start + halfStep h) →
        halfStep h = halfStep h0)
    (hbridge : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start →
      hexStripStaysInDir dregion R.start h0 ts) :
    R.DirectedStartIncidence h0 := by
  let S : HexStraightSide R.inRegion (hexStripInterior dregion)
      R.start h0 R.start :=
    hexStrip_straightSide dregion R.inRegion R.start h0 R.start (h0 + 3)
      (by
        intro h hint
        calc
          halfStep h = halfStep h0 := huniq h hint
          _ = halfStep ((h0 + 3) + 3) := by
            rw [show ((h0 + 3) + 3 : ℤ) = h0 + 6 by ring,
              hexStrip_halfStep_add6])
      hbridge
  exact R.directedStartIncidence_of_straightStart_reverse h0
    (hexStripInterior dregion) S (by
      change halfStep (h0 + 3) = -halfStep h0
      exact hexW1Exit_halfStep_add_three h0)


end HexFiniteRegion
end StatMech.Universality
