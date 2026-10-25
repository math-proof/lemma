/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Structure.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexAWGeometricOrbitData (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    HexFiniteStripGeometricOrbitData
      (I := HexAWPairIndex T L) (K := HexAWFixedIndex T L hT)
      (R := hexAWFiniteRegion T L hT) (h0 := 1)
      (hexAWDomainInteriorPairing T L hT hlocal) where
  heading v j := hexAWHeading v.1 j
  hgeom := by
    intro v j
    exact hexAWMid_sub_pos v.1 j
  startIncidence := hexAWStartIncidence T L hT
  start_mid := hexAWStartIncidence_mid T L hT
  start_heading := hexAWStartIncidence_heading T L hT
  neg i := i.1
  pos i := hexAWReflectIncidence i.1
  pair_ne := hexAWPairIndex_ne_reflect
  midpoint_reflect := by
    intro i
    change hexAWMid (hexAWReflectIncidence i.1).vtx.1
        (hexAWReflectIncidence i.1).edge =
      hsc_refl hexAWStart 1 (hexAWMid i.1.vtx.1 i.1.edge)
    rw [hexAW_refl_one_eq_four]
    exact hexAWReflectIncidence_mid i.1
  fixed k := k.1
  fixed_reflect := by
    intro k
    change hexAWMid k.1.vtx.1 k.1.edge =
      hsc_refl hexAWStart 1 (hexAWMid k.1.vtx.1 k.1.edge)
    rw [hexAW_refl_one_eq_four, ← hexAWReflectIncidence_mid,
      k.2.2.1]
  orbitPiece := hexAWOrbitPiece
  pair_piece := by intro i; rfl
  fixed_piece := by intro k; rfl
  boundary_partition := by
    rw [hexAWDomainInteriorPairing_interior]
    have hinc :
        (hexAWDomain T L hT hlocal).incidences =
          hexAWIncidences T L := by
      ext e
      simp [HexDomain.incidences]
    rw [hinc]
    simpa only [hexAWBoundaryIncidences] using
      hexAW_boundary_orbit_partition T L hT
  start_orbits_disjoint := hexAW_start_orbits_disjoint T L hT
  orbits_disjoint := hexAW_orbitPieces_pairwiseDisjoint T L hT


end
end StatMech.Universality
