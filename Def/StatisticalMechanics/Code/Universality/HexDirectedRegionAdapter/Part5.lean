/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Structure.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter


namespace StatMech.Universality

open Complex HexWalk


namespace HexStripDirectedStartData

noncomputable def toDirectedStartIncidence
    {M : Finset ℂ} {a : ℂ} {h0 : ℤ}
    (G : HexStripDirectedStartData M a h0) (ha : a ∈ M) :
    (hexStrip_finiteRegion M a ha).DirectedStartIncidence h0 := by
  refine HexFiniteRegion.directedStartIncidence_of_distinctMidpointStripStartGeometry
      (hexStrip_finiteRegion M a ha) h0 G.dregion G.uniqueInterior G.launch


noncomputable def toRegionDirectedStartIncidence
    (R : HexRegion) (M : Finset ℂ) (ha : R.start ∈ M) (h0 : ℤ)
    (G : HexStripDirectedStartData M R.start h0) :
    (hexStrip_region_finiteRegion R M ha).DirectedStartIncidence h0 := by
  simpa [hexStrip_region_finiteRegion] using G.toDirectedStartIncidence ha

end HexStripDirectedStartData


def hexDomainInwardDRegion {V : Type*} [DecidableEq V]
    (D : HexDomain V) (m : ℂ) (h : ℤ) : Prop :=
  ∃ e ∈ D.incidences,
    D.mid e.vtx e.edge = m ∧ D.pos e.vtx = m + halfStep h


end StatMech.Universality
