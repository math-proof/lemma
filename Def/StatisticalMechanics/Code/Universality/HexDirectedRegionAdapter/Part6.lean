/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter.Part4


namespace StatMech.Universality

open Complex HexWalk


noncomputable def hexDomainDirectedStartData_of_boundaryData
    {V : Type*} [DecidableEq V]
    (R : HexRegion) (M : Finset ℂ) (ha : R.start ∈ M) (h0 : ℤ)
    (D : HexDomain V) (P : D.InteriorPairing)
    (B : HexFiniteStripBoundaryData
      (hexStrip_region_finiteRegion R M ha) h0 D P)
    (hlaunch : hexDomainInwardDRegion D R.start h0)
    (huniq : ∀ h : ℤ,
      hexStripInteriorDistinctMidpoint (hexDomainInwardDRegion D)
          (R.start + halfStep h) →
        halfStep h = halfStep h0) :
    HexStripDirectedStartData M R.start h0 where
  dregion := hexDomainInwardDRegion D
  project := by
    intro m h hm
    rcases hm with ⟨e, he, hmid, _⟩
    rw [← hmid]
    simpa only [hexStrip_region_finiteRegion_mids] using B.mid_mem e he
  launch := hlaunch
  uniqueInterior := huniq


noncomputable def hexDomainDirectedStartIncidence_of_boundaryData
    {V : Type*} [DecidableEq V]
    (R : HexRegion) (M : Finset ℂ) (ha : R.start ∈ M) (h0 : ℤ)
    (D : HexDomain V) (P : D.InteriorPairing)
    (B : HexFiniteStripBoundaryData
      (hexStrip_region_finiteRegion R M ha) h0 D P)
    (hlaunch : hexDomainInwardDRegion D R.start h0)
    (huniq : ∀ h : ℤ,
      hexStripInteriorDistinctMidpoint (hexDomainInwardDRegion D)
          (R.start + halfStep h) →
        halfStep h = halfStep h0) :
    (hexStrip_region_finiteRegion R M ha).DirectedStartIncidence h0 :=
  (hexDomainDirectedStartData_of_boundaryData
    R M ha h0 D P B hlaunch huniq).toRegionDirectedStartIncidence
      R M ha h0

end StatMech.Universality
