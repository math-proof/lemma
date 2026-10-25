/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter.Part5


namespace StatMech.Universality

open Complex HexWalk


theorem hexDomainInwardDRegion_headingPeriodic
    {V : Type*} [DecidableEq V] (D : HexDomain V) :
    HexHeadingPeriodic (hexDomainInwardDRegion D) := by
  intro m h hm
  rcases hm with ⟨e, he, hmid, hpos⟩
  refine ⟨e, he, hmid, ?_⟩
  rw [hexStrip_halfStep_add6]
  exact hpos


theorem hexDomainInwardDRegion_project
    {V : Type*} [DecidableEq V] {R : HexFiniteRegion} {h0 : ℤ}
    {D : HexDomain V} {P : D.InteriorPairing}
    (B : HexFiniteStripBoundaryData R h0 D P)
    (m : ℂ) (h : ℤ) (hm : hexDomainInwardDRegion D m h) :
    R.inRegion m := by
  rcases hm with ⟨e, he, hmid, _⟩
  change m ∈ R.mids
  rw [← hmid]
  exact B.mid_mem e he


theorem hexDomainInwardDRegion_not_old_uniqueInterior
    {V : Type*} [DecidableEq V] (D : HexDomain V) (a : ℂ) (h0 : ℤ)
    (hstart : hexDomainInwardDRegion D a h0) :
    ¬(∀ h : ℤ, hexStripInterior (hexDomainInwardDRegion D)
        (a + halfStep h) → halfStep h = halfStep h0) :=
  not_hexStrip_uniqueInterior_of_headingPeriodic_start
    (hexDomainInwardDRegion D) a h0
    (hexDomainInwardDRegion_headingPeriodic D) hstart


end StatMech.Universality
