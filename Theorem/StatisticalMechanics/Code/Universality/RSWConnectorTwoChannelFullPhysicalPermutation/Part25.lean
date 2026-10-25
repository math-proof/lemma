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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part25
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_badCarrierSeparation_split
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hbad : RlcTwoChannelFullPhysicalBadCarrierSeparation
      gamma gamma' omega) :
    RlcTwoChannelFullPhysicalBadTargetSeparation gamma gamma' omega ∨
      RlcTwoChannelFullPhysicalBadSourceSeparation gamma gamma' omega := by
  obtain ⟨x, y, u, v, hx, hy, hxu, huv, hbad, hvy⟩ := hbad
  rw [rlc_twoChannelFullPhysical_not_carrierGeometry_iff] at hbad
  rcases hbad with htarget | hsource
  · left
    refine ⟨x, y, u, v, hx, hy, hxu, huv, ?_, hvy⟩
    rwa [← rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local]
  · right
    refine ⟨x, y, u, v, hx, hy, hxu, huv, ?_, hvy⟩
    rwa [← rlc_twoChannelFullPhysicalSourceCarrierGeometry_iff_local]


theorem rlc_twoChannelFullPhysical_goodComponent_or_badCarrierSeparation
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨
      RlcTwoChannelFullPhysicalBadCarrierSeparation gamma gamma' omega := by
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith omega hno
  obtain ⟨w⟩ := rlc_twoChannelFullFilledFaceBoundary_reachable
    gamma gamma' omega hxSupport hySupport
  rcases rlc_walk_subgraph_lift_or_first_exit_decomp
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega) w with
    ⟨q, _hq⟩ | ⟨u, v, q, r, huv, huvBad, _hdecomp⟩
  · exact Or.inl ⟨x, y, q.reachable, hxPath, hyPath⟩
  · right
    refine ⟨x, y, u, v, hxPath, hyPath, q.reachable, huv, ?_, r.reachable⟩
    intro hcarrier
    exact huvBad
      ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).2 ⟨huv, hcarrier⟩)


theorem rlc_twoChannelFullPhysical_goodComponent_or_badTarget_or_badSource
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨
      RlcTwoChannelFullPhysicalBadTargetSeparation gamma gamma' omega ∨
      RlcTwoChannelFullPhysicalBadSourceSeparation gamma gamma' omega := by
  rcases rlc_twoChannelFullPhysical_goodComponent_or_badCarrierSeparation
      gamma gamma' hfaith omega hno with hgood | hbad
  · exact Or.inl hgood
  · exact Or.inr
      (rlc_twoChannelFullPhysical_badCarrierSeparation_split hbad)


theorem rlc_twoChannelFullFilledBoundary_isCycles {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).IsCycles := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  let hH := rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega
  let x : Site 2 := gamma.1.1
  have hxK : x ∈ rlc_twoChannelFullReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega
      (rlc_path_start_mem_vertices gamma.1)
  have hxH : x ∈ H :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hxK
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box H hH
  let y : Site 2 := beacon 2 R
  have hyExt : y ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hyBox : y ∉ box 2 R := by
    simpa [exterior_eq_compl_box] using hyExt
  have hyH : y ∉ H := fun hy => hyBox (hR hy)
  intro f hf
  have hfSupport : f ∈ (faceBoundaryGraph H).support := by
    obtain ⟨g, hfg⟩ := hf
    exact hfg.mem_support_left
  rw [Set.ncard_eq_toFinset_card']
  apply faceBoundaryGraph_degree_eq_two_of_connected_complement
    H hH hxH hyH
  · intro a b ha hb
    exact rlc_twoChannelFullFilledReachSet_reachable_in_barrier
      gamma gamma' omega ha hb
  · intro a b ha hb
    apply rlc_twoChannelFullExteriorSet_reachable_in_filledBarrier
    · simpa [H, rlc_twoChannelFullFilledReachSet] using ha
    · simpa [H, rlc_twoChannelFullFilledReachSet] using hb
  · exact hfSupport


theorem rlc_twoChannelFullReachSet_subset_staticCut {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
    rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ⊆
      rlc_twoChannelFullPhysicalLiftVertexCut A := by
  intro z hz
  obtain ⟨hzBox, hzReach⟩ := hz
  change (openSubgraphInduce 2
    (rlc_twoChannelFullAmbientConfig gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (rect (-2 * n) (2 * n) (-n) n)).Reachable
      ⟨(rlc_connectorRightAnchor gamma : Site 2),
        (rlc_connectorRightAnchor gamma).2⟩ ⟨z, hzBox⟩ at hzReach
  rw [← rlc_openSub_twoChannelAugmented_forceTrace_eq_fullAmbientInduce,
    rlc_openSub_twoChannelAugmented_forceTrace] at hzReach
  obtain ⟨w⟩ := hzReach
  have hstart : (rlc_connectorRightAnchor gamma) ∈ A :=
    hAright _ (rlc_connectorRightAnchor_onRight gamma)
  have hpropagate {x y : RlcConnectorVertex n}
      (w : (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) ⊔
        rlc_connectorTraceWiring gamma gamma').Walk x y) :
      x ∈ A → y ∈ A := by
    intro hx
    induction w with
    | nil => exact hx
    | @cons u v t huv p ih =>
        have hv : v ∈ A := by
          rcases huv with hopen | htrace
          · rw [FK.openSub_adj] at hopen
            have hextend : rlc_twoChannelEdgeConfigExtend gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
                s(u, v) =
              rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
                ⟨s(u, v), hopen.1⟩ := by
              simp [rlc_twoChannelEdgeConfigExtend,
                rlc_twoChannelConfigSplitEquiv, hopen.1]
            have htrue :
                rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
                  ⟨s(u, v), hopen.1⟩ = true := by
              rw [← hextend]
              exact hopen.2
            exact
              ((rlc_twoChannelFullPhysicalCutInteriorConfig_true_iff
                gamma gamma' A ⟨s(u, v), hopen.1⟩).mp htrue u v rfl).2
          · have hno := rlc_twoChannel_traceWiring_not_crosses_staticCut
              gamma gamma' A hAright hAleft htrace
            tauto
        exact ih hv
  have hend : (⟨z, hzBox⟩ : RlcConnectorVertex n) ∈ A :=
    hpropagate w hstart
  exact ⟨hzBox, hend⟩


theorem rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj f g)
    (hcarrier : RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' f g) :
    ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      target.1.1.map Subtype.val =
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 := by
  let omega := rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hgood : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Adj f g :=
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
      gamma gamma' omega).2 ⟨hfg, hcarrier⟩
  obtain ⟨_hface, target, htarget⟩ := hgood
  let source := rlc_twoChannelFullPhysicalSourceEdge target
  let visible : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma' :=
    ⟨source, ⟨target, rfl⟩⟩
  have hsourceMap : source.1.map Subtype.val = sharedPrimalEdge f g := by
    calc
      source.1.map Subtype.val =
          rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) :=
        rlc_twoChannelFullPhysicalSourceEdge_map target
      _ = rlc_pimsEdgeEquiv
          s(rlc_dualReflect f, rlc_dualReflect g) := by rw [htarget]
      _ = sharedPrimalEdge f g :=
        rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge _ hfg
  have hclosed : omega source = false :=
    rlc_twoChannelFullPhysical_boundary_visibleSource_closed
      gamma gamma' omega hfg visible hsourceMap
  refine ⟨target, htarget, ?_⟩
  induction hedge : source.1 using Sym2.inductionOn with
  | _ u v =>
      have hsourceSite : s(u.1, v.1) = sharedPrimalEdge f g := by
        simpa [hedge, Sym2.map_mk] using hsourceMap
      obtain ⟨p, q, hshared, hpq⟩ :=
        sharedPrimalEdge_isLatticeEdge hfg.1
      have hbd := hfg.2
      rw [hshared, bdEdge_mk] at hbd
      let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
      have honeSite :
          p ∈ rlc_twoChannelFullPhysicalLiftVertexCut A ∨
            q ∈ rlc_twoChannelFullPhysicalLiftVertexCut A := by
        by_cases hpH : p ∈ H
        · left
          apply rlc_twoChannelFullReachSet_subset_staticCut
            gamma gamma' A hAright hAleft
          apply rlc_twoChannelFullFilledBoundary_inside_mem_reachSet
              gamma gamma' omega hpH (hbd.mp hpH)
          exact hpq
        · right
          have hqH : q ∈ H := by tauto
          apply rlc_twoChannelFullReachSet_subset_staticCut
            gamma gamma' A hAright hAleft
          apply rlc_twoChannelFullFilledBoundary_inside_mem_reachSet
              gamma gamma' omega hqH hpH
          exact hpq.symm
      have hsourcePQ : s(u.1, v.1) = s(p, q) :=
        hsourceSite.trans hshared
      rw [Sym2.eq_iff] at hsourcePQ
      have hone : u ∈ A ∨ v ∈ A := by
        rcases hsourcePQ with ⟨hup, hvq⟩ | ⟨huq, hvp⟩
        · rcases honeSite with hp | hq
          · exact Or.inl
              ((rlc_twoChannelFullPhysicalLiftVertexCut_mem A u).mp
                (by simpa [hup] using hp))
          · exact Or.inr
              ((rlc_twoChannelFullPhysicalLiftVertexCut_mem A v).mp
                (by simpa [hvq] using hq))
        · rcases honeSite with hp | hq
          · exact Or.inr
              ((rlc_twoChannelFullPhysicalLiftVertexCut_mem A v).mp
                (by simpa [hvp] using hp))
          · exact Or.inl
              ((rlc_twoChannelFullPhysicalLiftVertexCut_mem A u).mp
                (by simpa [huq] using hq))
      have hnotBoth : ¬(u ∈ A ∧ v ∈ A) := by
        intro huv
        have htrue : omega source = true :=
          (rlc_twoChannelFullPhysicalCutInteriorConfig_true_iff
            gamma gamma' A source).2 (by
              intro a b hab
              rw [hedge, Sym2.eq_iff] at hab
              rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact huv
              · exact huv.symm)
        rw [hclosed] at htrue
        contradiction
      exact ⟨u, v, rfl, by tauto⟩


end
end StatMech.Universality
