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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part22
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalSourceCarrierGeometry_iff_local
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (f g : Site 2) :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g ↔
      RlcTwoChannelFullPhysicalSourceCarrierLocal gamma gamma' f g := by
  constructor
  · rintro ⟨source, hsource⟩
    induction hedge : source.1 using Sym2.inductionOn with
    | _ x y =>
        have hxy : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y :=
          (SimpleGraph.mem_edgeSet _).mp (hedge ▸ source.2)
        exact ⟨x, y, x.2, y.2, by simpa [hedge, Sym2.map_mk] using hsource.symm,
          hxy⟩
  · rintro ⟨p, q, hp, hq, hshared, hpq⟩
    let source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
      ⟨s(⟨p, hp⟩, ⟨q, hq⟩), (SimpleGraph.mem_edgeSet _).mpr hpq⟩
    exact ⟨source, by simpa [source, Sym2.map_mk] using hshared.symm⟩

theorem rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (f g : Site 2) :
    RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g ↔
      RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g ∧
        RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g := by
  constructor
  · rintro ⟨target, source, htarget, hsource⟩
    exact ⟨⟨target, htarget⟩, source, hsource⟩
  · rintro ⟨⟨target, htarget⟩, source, hsource⟩
    exact ⟨target, source, htarget, hsource⟩


theorem rlc_twoChannelFullPhysical_boundaryCarrierGeometry_comm
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) :
    RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g ↔
      RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' g f := by
  constructor
  · rintro ⟨target, source, htarget, hsource⟩
    refine ⟨target, source, ?_, ?_⟩
    · simpa [Sym2.eq_swap] using htarget
    · rw [← sharedPrimalEdge_comm_of_adj hfg]
      exact hsource
  · rintro ⟨target, source, htarget, hsource⟩
    refine ⟨target, source, ?_, ?_⟩
    · simpa [Sym2.eq_swap] using htarget
    · rw [sharedPrimalEdge_comm_of_adj hfg]
      exact hsource


theorem rlc_twoChannelFullPhysical_firstBad_eq_of_sharedSourceEdge
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {ur vr f g : Site 2}
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = sharedPrimalEdge ur vr)
    (hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' ur vr) :
    s(f, g) = s(ur, vr) ∧
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
        gamma gamma' f g := by
  have hedge : s(f, g) = s(ur, vr) :=
    (jce_sharedPrimalEdge_inj hfg hurv).2 hshared
  refine ⟨hedge, ?_⟩
  intro hcarrier
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hbad hcarrier
  · exact hbad
      ((rlc_twoChannelFullPhysical_boundaryCarrierGeometry_comm
        gamma gamma' hurv).2 hcarrier)


theorem rlc_twoChannelFullPhysical_not_carrierGeometry_iff
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (f g : Site 2) :
    ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g ↔
      (¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g ∨
        ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) := by
  rw [rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source]
  tauto


theorem rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g : Site 2} :
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Adj f g ↔
      (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g ∧
        RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g := by
  constructor
  · rintro ⟨hfg, target, htarget⟩
    let source := rlc_twoChannelFullPhysicalSourceEdge target
    refine ⟨hfg, target.1, source, htarget, ?_⟩
    calc
      source.1.map Subtype.val =
          rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) :=
        rlc_twoChannelFullPhysicalSourceEdge_map target
      _ = rlc_pimsEdgeEquiv
          s(rlc_dualReflect f, rlc_dualReflect g) := by rw [htarget]
      _ = sharedPrimalEdge f g :=
        rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega) hfg
  · rintro ⟨hfg, target, source, htarget, hsource⟩
    have hpims : rlc_pimsEdgeEquiv
        s(rlc_dualReflect f, rlc_dualReflect g) = sharedPrimalEdge f g :=
      rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega) hfg
    have hsourceMap : source.1.map Subtype.val =
        rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by
      calc
        source.1.map Subtype.val = sharedPrimalEdge f g := hsource
        _ = rlc_pimsEdgeEquiv
            s(rlc_dualReflect f, rlc_dualReflect g) := hpims.symm
        _ = rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by rw [htarget]
    let physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' :=
      ⟨target, ⟨⟨source, hsourceMap⟩⟩⟩
    exact ⟨hfg, physical, htarget⟩


end
end StatMech.Universality
