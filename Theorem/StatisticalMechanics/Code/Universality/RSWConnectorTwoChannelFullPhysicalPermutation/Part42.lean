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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part42
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_firstIntersectionOrderedContacts_of_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelFullPhysicalFirstIntersectionOrderedContacts
      gamma gamma' omega := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  obtain ⟨z, right, left, flipLeft, _preFlipLeft,
      hzRight, hzLeft, _hrightEdges, _hleftEdges, _hflipLeftEdges,
      _hinter, hflipLeftSupport, hflipLeftRank, _hpreRightInter,
      _hpreSuffixInter,
      _hprePositive, _hrightPath, _hleftPath, _hflipLeftPath,
      _hpreFlipLeftPath, _hleftMappedSplit, _hrightHalfPath,
      hrankRealized, hglobalMin⟩ :=
    rlc_bookFirstIntersection_truncatedSides_of_faithful
      gamma gamma' hfaith
  let flipRight : (hypercubicLattice 2).Walk
      (rlc_flipX (gamma.1.1 : Site 2)) (rlc_flipX z) :=
    right.map rlc_flipXLatticeHom
  have hrightStartFlip : rlc_flipX (gamma.1.1 : Site 2) =
      (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  have hrightStartH : rlc_flipX (gamma.1.1 : Site 2) ∈ H := by
    rw [hrightStartFlip]
    exact rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
      (rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega
        (rlc_path_start_mem_vertices gamma.1))
  have hzFlipExt :=
    rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hzLeft
  have hzFlipOut : rlc_flipX z ∉ H := by
    simpa [H, rlc_twoChannelFullFilledReachSet] using hzFlipExt
  have hflipRightTrace : ∀ v ∈ flipRight.support,
      ∃ w ∈ rlc_pathVertices gamma.1, rlc_flipX w = v := by
    intro v hv
    change v ∈ (right.map rlc_flipXLatticeHom).support at hv
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
    obtain ⟨w, hw, hwv⟩ := hv
    change rlc_flipX w = v at hwv
    subst v
    refine ⟨w, ?_, rfl⟩
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hw
    rcases hw with rfl | ⟨e, he, hwe⟩
    · exact hzRight
    · induction e using Sym2.inductionOn with
      | _ a b =>
          have habPath := rlc_pathEdge_endpoints_mem_vertices gamma.1
            (_hrightEdges s(a, b) he)
          rw [Sym2.mem_iff] at hwe
          exact hwe.elim (fun h => h ▸ habPath.1) (fun h => h ▸ habPath.2)
  obtain ⟨x, hxSupport, hxPath, hxOrder⟩ :=
    rlc_faceBoundary_orderedContact_of_flippedTraceWalk_exit
      gamma.1 H flipRight hflipRightTrace hrightStartH hzFlipOut
  have hzH : z ∈ H :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
      (rlc_rightPathVertex_mem_twoChannelFullReachSet
        gamma gamma' omega hzRight)
  have hleftEndPath : (gamma'.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    rlc_connector_path_end_mem_vertices gamma'.1
  have hleftEndExt :=
    rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hleftEndPath
  have hleftEndFlip : rlc_flipX (gamma'.1.2.1 : Site 2) =
      (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hleftEndOut : rlc_flipX (gamma'.1.2.1 : Site 2) ∉ H := by
    rw [hleftEndFlip]
    simpa [H, rlc_twoChannelFullFilledReachSet] using hleftEndExt
  let flipLeftOrdered : (hypercubicLattice 2).Walk
      (rlc_flipX (rlc_flipX z))
      (rlc_flipX (gamma'.1.2.1 : Site 2)) :=
    flipLeft.copy (rlc_flipX_involutive z).symm hleftEndFlip.symm
  have hflipLeftTrace : ∀ v ∈ flipLeftOrdered.support,
      ∃ w ∈ rlc_pathVertices gamma'.1, rlc_flipX w = v := by
    intro v hv
    have hv' : v ∈ flipLeft.support := by
      simpa [flipLeftOrdered, SimpleGraph.Walk.support_copy] using hv
    let w := rlc_flipX v
    have hwLeft : w ∈ left.support := hflipLeftSupport v |>.1 hv'
    have hwPath : w ∈ rlc_pathVertices gamma'.1 := by
      rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hwLeft
      rcases hwLeft with hwend | ⟨e, he, hwe⟩
      · rw [hwend]
        exact hleftEndPath
      · induction e using Sym2.inductionOn with
        | _ a b =>
            have habPath := rlc_pathEdge_endpoints_mem_vertices gamma'.1
              (_hleftEdges s(a, b) he)
            rw [Sym2.mem_iff] at hwe
            exact hwe.elim (fun h => h ▸ habPath.1) (fun h => h ▸ habPath.2)
    exact ⟨w, hwPath, by simp [w]⟩
  have hzFlipFlipH : rlc_flipX (rlc_flipX z) ∈ H := by
    simpa using hzH
  obtain ⟨y, hySupport, hyPath, hyOrder⟩ :=
    rlc_faceBoundary_orderedContact_of_flippedTraceWalk_exit
      gamma'.1 H flipLeftOrdered hflipLeftTrace hzFlipFlipH hleftEndOut
  have hyOrder' : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support := by
    simpa [flipLeftOrdered, SimpleGraph.Walk.support_copy] using hyOrder
  have hfirstRetained : ∀ w ∈ right.support,
      rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z := by
    intro w hwRight hwLeft
    by_cases hwSuffix : w ∈ flipLeft.support
    · exact _hinter w hwRight hwSuffix
    · apply _hpreRightInter w ?_ hwRight
      have hwWhole : rlc_flipX w ∈
          (rlc_ambientCrossingWalk gamma'.1).support :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 (rlc_flipX w)).2 hwLeft
      have hwMapped : w ∈ ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map]
        refine ⟨rlc_flipX w, hwWhole, ?_⟩
        change rlc_flipX (rlc_flipX w) = w
        exact rlc_flipX_involutive w
      rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hwMapped
      rcases hwMapped with hwend | ⟨e, he, hwe⟩
      · exfalso
        apply hwSuffix
        rw [hwend]
        change rlc_flipX (gamma'.1.2.1 : Site 2) ∈ flipLeft.support
        rw [hleftEndFlip]
        exact flipLeft.end_mem_support
      · rcases _hleftMappedSplit e he with hePre | heSuffix
        · induction e using Sym2.inductionOn with
          | _ a b =>
              rw [Sym2.mem_iff] at hwe
              have ha := _preFlipLeft.fst_mem_support_of_mem_edges hePre
              have hb := _preFlipLeft.snd_mem_support_of_mem_edges hePre
              exact hwe.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
        · exfalso
          apply hwSuffix
          induction e using Sym2.inductionOn with
          | _ a b =>
              rw [Sym2.mem_iff] at hwe
              have ha := flipLeft.fst_mem_support_of_mem_edges heSuffix
              have hb := flipLeft.snd_mem_support_of_mem_edges heSuffix
              exact hwe.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
  exact ⟨z, x, y, right, flipLeft, hzRight, hzLeft,
    hxSupport, hySupport, hxPath, hyPath, hxOrder, hyOrder', hflipLeftRank,
    hfirstRetained, hrankRealized, hglobalMin⟩


end
end StatMech.Universality
