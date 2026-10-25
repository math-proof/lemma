/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part23
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_crossedVisible
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {S : Set (Site 2)}
    {f g : Site 2} (hfg : (faceBoundaryGraph S).Adj f g) :
    RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g ↔
      RlcTwoChannelFullPhysicalCrossedVisibleSourceGeometry
        gamma gamma' f g := by
  have hpims : rlc_pimsEdgeEquiv
      s(rlc_dualReflect f, rlc_dualReflect g) = sharedPrimalEdge f g :=
    rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge S hfg
  constructor
  · rintro ⟨target, source, htarget, hsource⟩
    let physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' :=
      ⟨target, ⟨⟨source, by
        calc
          source.1.map Subtype.val = sharedPrimalEdge f g := hsource
          _ = rlc_pimsEdgeEquiv
              s(rlc_dualReflect f, rlc_dualReflect g) := hpims.symm
          _ = rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by rw [htarget]
        ⟩⟩⟩
    have hsourceEq : rlc_twoChannelFullPhysicalSourceEdge physical = source := by
      apply Subtype.ext
      apply Sym2.map.injective Subtype.val_injective
      calc
        (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val =
            rlc_pimsEdgeEquiv (physical.1.1.map Subtype.val) :=
          rlc_twoChannelFullPhysicalSourceEdge_map physical
        _ = rlc_pimsEdgeEquiv
            s(rlc_dualReflect f, rlc_dualReflect g) := by rw [htarget]
        _ = sharedPrimalEdge f g := hpims
        _ = source.1.map Subtype.val := hsource.symm
    let visible : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma' :=
      ⟨source, ⟨physical, hsourceEq⟩⟩
    exact ⟨visible, hsource⟩
  · rintro ⟨visible, hsource⟩
    obtain ⟨target, htargetSource⟩ := visible.2
    have htarget : target.1.1.map Subtype.val =
        s(rlc_dualReflect f, rlc_dualReflect g) := by
      apply rlc_pimsEdgeEquiv.injective
      calc
        rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) =
            (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val :=
          (rlc_twoChannelFullPhysicalSourceEdge_map target).symm
        _ = visible.1.1.map Subtype.val := by rw [htargetSource]
        _ = sharedPrimalEdge f g := hsource
        _ = rlc_pimsEdgeEquiv
            s(rlc_dualReflect f, rlc_dualReflect g) := hpims.symm
    exact ⟨target.1, visible.1, htarget, hsource⟩

theorem rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_crossedVisible
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g : Site 2} :
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Adj f g ↔
      (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g ∧
      RlcTwoChannelFullPhysicalCrossedVisibleSourceGeometry
        gamma gamma' f g := by
  rw [rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry]
  constructor
  · rintro ⟨hfg, hcarrier⟩
    exact ⟨hfg,
      (rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_crossedVisible
        gamma gamma' hfg).1 hcarrier⟩
  · rintro ⟨hfg, hvisible⟩
    exact ⟨hfg,
      (rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_crossedVisible
        gamma gamma' hfg).2 hvisible⟩


theorem rlc_twoChannelFullPhysical_boundary_visibleSource_closed
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma')
    (hsource : source.1.1.map Subtype.val = sharedPrimalEdge f g) :
    omega source.1 = false := by
  have hopen := rlc_twoChannelFullFilledBoundary_le_openFaceDual
    gamma gamma' omega hfg
  rw [openSubgraph_adj] at hopen
  have hclosed := hopen.2
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1,
    ← hsource, rlc_twoChannelFullAmbientConfig_source] at hclosed
  simpa using hclosed


end
end StatMech.Universality
