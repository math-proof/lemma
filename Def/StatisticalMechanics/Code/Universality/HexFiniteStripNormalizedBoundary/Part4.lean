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
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part5


namespace StatMech.Universality

open Complex HexWalk


namespace HexFiniteRegion

noncomputable def hexStrip_singleRegion_directedStartIncidence
    (a : ℂ) (h0 : ℤ) :
    (hexStrip_singleRegion a).DirectedStartIncidence h0 where
  dregion := fun m h => m = a ∧ halfStep h = halfStep h0
  project := by
    intro m h hm
    simp [hexStrip_singleRegion, hexStrip_finiteRegion,
      HexFiniteRegion.inRegion, hm.1]
  walksInDirectedRegion := by
    intro ts hlegal hstay
    have hnil := hexStrip_singleRegion_legal_stays_eq_nil a h0 ts hlegal hstay
    subst hnil
    intro p hp
    simp only [hexStripDirMids_nil, List.mem_singleton] at hp
    subst p
    exact ⟨rfl, rfl⟩
  start_exact := by
    intro h hh
    exact hh.2


end HexFiniteRegion
end StatMech.Universality
