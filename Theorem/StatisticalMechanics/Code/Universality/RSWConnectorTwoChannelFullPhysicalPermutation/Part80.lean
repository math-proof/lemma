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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part79
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_bookRowOnePhysicalTraceNetworkBracket_exteriorPoint_mem
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1) :
    rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈
      (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).support := by
  simp only [rlc_bookRowOnePhysicalTraceNetworkBracket,
    SimpleGraph.Walk.support_copy,
    rlc_bookSimplePhysicalTraceNetworkBracket]
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hzRight
    (s := rlc_flipX (gamma'.1.2.1 : Site 2))
      (rlc_bookRowOne_flippedLeftEndpoint_mem gamma')
  change rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈
    (S.map rlc_dualReflectSymmLatticeHom).support
  rw [SimpleGraph.Walk.support_map rlc_dualReflectSymmLatticeHom S,
    List.mem_map]
  exact ⟨![(2 * n + 2), n + 2],
    rlc_bookSimpleTraceNetworkBracket_exteriorPoint_mem
      gamma gamma' hzRight
        (rlc_bookRowOne_flippedLeftEndpoint_mem gamma'), rfl⟩


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_isPath
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1) :
    (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).IsPath := by
  simpa only [rlc_bookRowOnePhysicalTraceNetworkBracket,
    SimpleGraph.Walk.isPath_copy] using
      (rlc_bookSimplePhysicalTraceNetworkBracket_isPath
        hn hfaith hzRight (s := rlc_flipX (gamma'.1.2.1 : Site 2))
          (rlc_bookRowOne_flippedLeftEndpoint_mem gamma'))


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_right_index_le_exterior
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1) {j : Nat}
    (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).length)
    (hjRight : rlc_dualReflect
      ((rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert j) ∈ rlc_pathVertices gamma.1) :
    j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support.idxOf
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) := by
  let hsLeft := rlc_bookRowOne_flippedLeftEndpoint_mem gamma'
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hzRight hsLeft
  let P := rlc_bookSimplePhysicalTraceNetworkBracket
    gamma gamma' hzRight hsLeft
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight
  let d : Site 2 := ![2 * n + 2, n + 2]
  have hBSupport : B.support = P.support := by
    simp only [B, P, rlc_bookRowOnePhysicalTraceNetworkBracket,
      SimpleGraph.Walk.support_copy]
  have hBLength : B.length = P.length := by
    simp only [B, P, rlc_bookRowOnePhysicalTraceNetworkBracket,
      SimpleGraph.Walk.length_copy]
  have hBGet : B.getVert j = P.getVert j := by
    simp only [B, P, rlc_bookRowOnePhysicalTraceNetworkBracket,
      SimpleGraph.Walk.getVert_copy]
  have hPS : P = S.map rlc_dualReflectSymmLatticeHom := rfl
  have hdS : d ∈ S.support :=
    rlc_bookSimpleTraceNetworkBracket_exteriorPoint_mem
      gamma gamma' hzRight hsLeft
  have hgetMap : P.getVert j = rlc_dualReflect.symm (S.getVert j) := by
    rw [hPS]
    exact SimpleGraph.Walk.getVert_map rlc_dualReflectSymmLatticeHom S j
  have hjSourceRight : S.getVert j ∈ rlc_pathVertices gamma.1 := by
    have hEq : rlc_dualReflect (B.getVert j) = S.getVert j := by
      calc
        _ = rlc_dualReflect (P.getVert j) :=
          congrArg rlc_dualReflect hBGet
        _ = rlc_dualReflect (rlc_dualReflect.symm (S.getVert j)) :=
          congrArg rlc_dualReflect hgetMap
        _ = _ := rlc_dualReflect.apply_symm_apply _
    exact hEq ▸ hjRight
  have hjPrefix : S.getVert j ∈ (S.takeUntil d hdS).support :=
    rlc_bookSimpleTraceNetworkBracket_right_mem_exteriorPrefix
      hn hfaith hzRight hsLeft (S.getVert_mem_support j) hjSourceRight hdS
  have hidxSource : S.support.idxOf (S.getVert j) ≤ S.support.idxOf d :=
    rlc_idxOf_le_of_mem_takeUntil S hdS hjPrefix
  have hidxMap (x : Site 2) :
      P.support.idxOf (rlc_dualReflect.symm x) = S.support.idxOf x := by
    rw [hPS]
    have hsupp : (S.map rlc_dualReflectSymmLatticeHom).support =
        S.support.map rlc_dualReflect.symm :=
      SimpleGraph.Walk.support_map rlc_dualReflectSymmLatticeHom S
    calc
      (S.map rlc_dualReflectSymmLatticeHom).support.idxOf
          (rlc_dualReflect.symm x) =
          (S.support.map rlc_dualReflect.symm).idxOf
            (rlc_dualReflect.symm x) :=
        congrArg (fun l => l.idxOf (rlc_dualReflect.symm x)) hsupp
      _ = S.support.idxOf x := rlc_list_idxOf_map_of_injective _
        rlc_dualReflect.symm.injective _ _
  have hPPath := rlc_bookSimplePhysicalTraceNetworkBracket_isPath
    hn hfaith hzRight hsLeft
  have hidxJ : P.support.idxOf (P.getVert j) = j :=
    rlc_isPath_idxOf_getVert P hPPath j (by
      rw [← hBLength]
      exact hjLength)
  change j ≤ B.support.idxOf (rlc_dualReflect.symm d)
  calc
    j = P.support.idxOf (P.getVert j) := hidxJ.symm
    _ = P.support.idxOf (rlc_dualReflect.symm (S.getVert j)) :=
      congrArg P.support.idxOf hgetMap
    _ = S.support.idxOf (S.getVert j) := hidxMap _
    _ ≤ S.support.idxOf d := hidxSource
    _ = P.support.idxOf (rlc_dualReflect.symm d) := (hidxMap _).symm
    _ = B.support.idxOf (rlc_dualReflect.symm d) := by rw [hBSupport]


theorem rlc_bookSimpleTraceNetworkBracket_left_index_ge_exterior
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {r s w : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hw : w ∈ (rlc_bookSimpleTraceNetworkBracket
      gamma gamma' hr hsLeft).support)
    (hwLeft : w ∈ rlc_pathVertices gamma'.1) :
    (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support.idxOf
        (![(2 * n + 2), n + 2] : Site 2) ≤
      (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support.idxOf
        w := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hrWR : r ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr
  have hsWL : rlc_flipX s ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft
  let P := WR.dropUntil r hrWR
  let D := rlc_bookExteriorEndpointDetour gamma gamma'
  let Q := WL.takeUntil (rlc_flipX s) hsWL
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft
  let d : Site 2 := ![2 * n + 2, n + 2]
  have hdD : d ∈ D.support :=
    rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'
  have hdP : d ∉ P.support := by
    intro hd
    have hdWR := WR.support_dropUntil_subset hrWR hd
    have hdPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 d).1 hdWR
    have hdBox := rlc_pathVertex_mem_rect gamma.1 hdPath
    rw [mem_rect] at hdBox
    simp [d] at hdBox
  have hdPD : d ∈ (P.append D).support :=
    SimpleGraph.Walk.subset_support_append_right P D hdD
  have hdS : d ∈ S.support :=
    rlc_bookSimpleTraceNetworkBracket_exteriorPoint_mem
      gamma gamma' hr hsLeft
  have hdS' : d ∈ ((P.append D).append Q).support :=
    SimpleGraph.Walk.subset_support_append_left (P.append D) Q hdPD
  have htakePD : (P.append D).takeUntil d hdPD =
      P.append (D.takeUntil d hdD) :=
    rlc_walk_takeUntil_append_of_notMem_left P D hdP hdD
  have htakeS : ((P.append D).append Q).takeUntil d hdS' =
      P.append (D.takeUntil d hdD) := by
    rw [SimpleGraph.Walk.takeUntil_append_of_mem_left]
    exact htakePD
  change S.support.idxOf d ≤ S.support.idxOf w
  by_contra hnot
  have hwd : S.support.idxOf w ≤ S.support.idxOf d := by omega
  have hwPrefix : w ∈ (S.takeUntil d hdS).support :=
    (rlc_mem_takeUntil_iff_idxOf_le S hdS hw).2 hwd
  have hwPrefix' : w ∈ (P.append (D.takeUntil d hdD)).support := by
    have hwPrefix'' : w ∈
        (((P.append D).append Q).takeUntil d hdS').support := by
      simpa only [S] using hwPrefix
    simpa only [htakeS] using hwPrefix''
  rw [SimpleGraph.Walk.mem_support_append_iff] at hwPrefix'
  rcases hwPrefix' with hwP | hwDprefix
  · have hwWR := WR.support_dropUntil_subset hrWR hwP
    have hwRight :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 w).1 hwWR
    exact (Finset.disjoint_left.mp hfaith.exposed_disjoint) hwRight hwLeft
  · have hwD : w ∈ D.support :=
      D.support_takeUntil_subset_support hdD hwDprefix
    have hwEnd := rlc_bookExteriorEndpointDetour_meets_leftBox_only_endpoint
      hn gamma gamma' hwD (rlc_pathVertex_mem_rect gamma'.1 hwLeft)
    have hEndLe : D.support.idxOf (gamma'.1.1 : Site 2) ≤
        D.support.idxOf d := by
      simpa [hwEnd] using rlc_idxOf_le_of_mem_takeUntil D hdD hwDprefix
    have hEndIdx : D.support.idxOf (gamma'.1.1 : Site 2) = D.length :=
      rlc_isPath_idxOf_end D
        (rlc_bookExteriorEndpointDetour_isPath hn gamma gamma')
    have hdIdxLt : D.support.idxOf d < D.length := by
      have hdIdxSupport := List.idxOf_lt_length_of_mem hdD
      rw [SimpleGraph.Walk.length_support] at hdIdxSupport
      have hdNeEnd : d ≠ (gamma'.1.1 : Site 2) := by
        intro heq
        have h0 := congrArg (fun z : Site 2 => z 0) heq
        dsimp only [d] at h0
        simp only [Matrix.cons_val_zero] at h0
        have hl0 : (gamma'.1.1 : Site 2) 0 = -2 * n := gamma'.1.1.2.2
        omega
      have hdIdxNe : D.support.idxOf d ≠ D.length := by
        intro heq
        have hidx : D.support.idxOf d =
            D.support.idxOf (gamma'.1.1 : Site 2) := by
          rw [hEndIdx]
          exact heq
        exact hdNeEnd ((List.idxOf_inj hdD).1 hidx)
      omega
    omega

theorem rlc_bookRowOnePhysicalTraceNetworkBracket_left_index_ge_exterior
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1) {j : Nat}
    (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).length)
    (hjLeft : rlc_dualReflect
      ((rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert j) ∈ rlc_pathVertices gamma'.1) :
    (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support.idxOf
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) ≤ j := by
  let hsLeft := rlc_bookRowOne_flippedLeftEndpoint_mem gamma'
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hzRight hsLeft
  let P := rlc_bookSimplePhysicalTraceNetworkBracket
    gamma gamma' hzRight hsLeft
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight
  let d : Site 2 := ![2 * n + 2, n + 2]
  have hBSupport : B.support = P.support := by
    simp only [B, P, rlc_bookRowOnePhysicalTraceNetworkBracket,
      SimpleGraph.Walk.support_copy]
  have hBLength : B.length = P.length := by
    simp only [B, P, rlc_bookRowOnePhysicalTraceNetworkBracket,
      SimpleGraph.Walk.length_copy]
  have hBGet : B.getVert j = P.getVert j := by
    simp only [B, P, rlc_bookRowOnePhysicalTraceNetworkBracket,
      SimpleGraph.Walk.getVert_copy]
  have hPS : P = S.map rlc_dualReflectSymmLatticeHom := rfl
  have hgetMap : P.getVert j = rlc_dualReflect.symm (S.getVert j) := by
    rw [hPS]
    exact SimpleGraph.Walk.getVert_map rlc_dualReflectSymmLatticeHom S j
  have hjSourceLeft : S.getVert j ∈ rlc_pathVertices gamma'.1 := by
    have hEq : rlc_dualReflect (B.getVert j) = S.getVert j := by
      calc
        _ = rlc_dualReflect (P.getVert j) :=
          congrArg rlc_dualReflect hBGet
        _ = rlc_dualReflect (rlc_dualReflect.symm (S.getVert j)) :=
          congrArg rlc_dualReflect hgetMap
        _ = _ := rlc_dualReflect.apply_symm_apply _
    exact hEq ▸ hjLeft
  have hidxSource :=
    rlc_bookSimpleTraceNetworkBracket_left_index_ge_exterior
      hn hfaith hzRight hsLeft (S.getVert_mem_support j) hjSourceLeft
  have hidxMap (x : Site 2) :
      P.support.idxOf (rlc_dualReflect.symm x) = S.support.idxOf x := by
    rw [hPS]
    have hsupp : (S.map rlc_dualReflectSymmLatticeHom).support =
        S.support.map rlc_dualReflect.symm :=
      SimpleGraph.Walk.support_map rlc_dualReflectSymmLatticeHom S
    calc
      (S.map rlc_dualReflectSymmLatticeHom).support.idxOf
          (rlc_dualReflect.symm x) =
          (S.support.map rlc_dualReflect.symm).idxOf
            (rlc_dualReflect.symm x) :=
        congrArg (fun l => l.idxOf (rlc_dualReflect.symm x)) hsupp
      _ = S.support.idxOf x := rlc_list_idxOf_map_of_injective _
        rlc_dualReflect.symm.injective _ _
  have hPPath := rlc_bookSimplePhysicalTraceNetworkBracket_isPath
    hn hfaith hzRight hsLeft
  have hidxJ : P.support.idxOf (P.getVert j) = j :=
    rlc_isPath_idxOf_getVert P hPPath j (by
      rw [← hBLength]
      exact hjLength)
  change B.support.idxOf (rlc_dualReflect.symm d) ≤ j
  calc
    B.support.idxOf (rlc_dualReflect.symm d) =
        P.support.idxOf (rlc_dualReflect.symm d) := by rw [hBSupport]
    _ = S.support.idxOf d := hidxMap _
    _ ≤ S.support.idxOf (S.getVert j) := hidxSource
    _ = P.support.idxOf (rlc_dualReflect.symm (S.getVert j)) :=
      (hidxMap _).symm
    _ = P.support.idxOf (P.getVert j) :=
      congrArg P.support.idxOf hgetMap.symm
    _ = j := hidxJ


theorem rlc_bookExteriorEndpointDetour_takeUntil_topRight
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    let D := rlc_bookExteriorEndpointDetour gamma gamma'
    let d : Site 2 := ![2 * n + 2, n + 2]
    let hd : d ∈ D.support :=
      rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'
    ∀ v ∈ (D.takeUntil d hd).support, 2 * n ≤ v 0 := by
  dsimp only
  let r : Site 2 := gamma.1.2.1
  have hr : (![r 0, r 1] : Site 2) = r := by
    ext i
    fin_cases i <;> simp
  let R : (hypercubicLattice 2).Walk r ![2 * n + 2, n + 2] :=
    (sw_lshape (r 0) (r 1) (2 * n + 2) (n + 2)).copy hr rfl
  let T : (hypercubicLattice 2).Walk
      ![2 * n + 2, n + 2] ![-2 * n - 2, n + 2] :=
    sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2)
  let l : Site 2 := gamma'.1.1
  have hl : (![l 0, l 1] : Site 2) = l := by
    ext i
    fin_cases i <;> simp
  let L : (hypercubicLattice 2).Walk ![-2 * n - 2, n + 2] l :=
    ((sw_lshape (l 0) (l 1) (-2 * n - 2) (n + 2)).reverse).copy
      rfl hl
  let D := rlc_bookExteriorEndpointDetour gamma gamma'
  let d : Site 2 := ![2 * n + 2, n + 2]
  have hD : D = (R.append T).append L := by rfl
  have hdR : d ∈ R.support := R.end_mem_support
  have hdRT : d ∈ (R.append T).support :=
    SimpleGraph.Walk.subset_support_append_left R T hdR
  have hdD : d ∈ D.support :=
    rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'
  intro v hv
  have hvRT : v ∈ ((R.append T).takeUntil d hdRT).support := by
    rw [← SimpleGraph.Walk.takeUntil_append_of_mem_left
      (R.append T) L hdRT]
    simpa only [hD] using hv
  have hvR : v ∈ (R.takeUntil d hdR).support := by
    rw [← SimpleGraph.Walk.takeUntil_append_of_mem_left R T hdR]
    exact hvRT
  have hvRSupport := R.support_takeUntil_subset_support hdR hvR
  dsimp only [R] at hvRSupport
  rw [SimpleGraph.Walk.support_copy, sw_lshape_mem_support] at hvRSupport
  rcases hvRSupport with hvHoriz | hvVert
  · rw [sw_horizSeg_mem_support] at hvHoriz
    obtain ⟨t, ht, rfl⟩ := hvHoriz
    rw [Set.mem_uIcc] at ht
    simp only [Matrix.cons_val_zero]
    have hr0 : r 0 = 2 * n := gamma.1.2.1.2.2
    rcases ht with ht | ht <;> omega
  · rw [sw_vertSeg_mem_support] at hvVert
    obtain ⟨t, _ht, rfl⟩ := hvVert
    simp only [Matrix.cons_val_zero]
    omega

theorem rlc_bookSimpleTraceNetworkBracket_collar_index_ge_exterior
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {r s : Site 2} (hr : r ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hcollar : (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) ∈
      (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support) :
    (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support.idxOf
        (![(2 * n + 2), n + 2] : Site 2) ≤
      (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support.idxOf
        (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hrWR : r ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr
  have hsWL : rlc_flipX s ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft
  let P := WR.dropUntil r hrWR
  let D := rlc_bookExteriorEndpointDetour gamma gamma'
  let Q := WL.takeUntil (rlc_flipX s) hsWL
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft
  let d : Site 2 := ![2 * n + 2, n + 2]
  let w : Site 2 := ![-2 * n - 1, (gamma'.1.1 : Site 2) 1]
  have hdD : d ∈ D.support :=
    rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'
  have hdP : d ∉ P.support := by
    intro hd
    have hdWR := WR.support_dropUntil_subset hrWR hd
    have hdPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 d).1 hdWR
    have hdBox := rlc_pathVertex_mem_rect gamma.1 hdPath
    rw [mem_rect] at hdBox
    simp [d] at hdBox
  have hdPD : d ∈ (P.append D).support :=
    SimpleGraph.Walk.subset_support_append_right P D hdD
  have hdS : d ∈ S.support :=
    rlc_bookSimpleTraceNetworkBracket_exteriorPoint_mem
      gamma gamma' hr hsLeft
  have hdS' : d ∈ ((P.append D).append Q).support :=
    SimpleGraph.Walk.subset_support_append_left (P.append D) Q hdPD
  have htakePD : (P.append D).takeUntil d hdPD =
      P.append (D.takeUntil d hdD) :=
    rlc_walk_takeUntil_append_of_notMem_left P D hdP hdD
  have htakeS : ((P.append D).append Q).takeUntil d hdS' =
      P.append (D.takeUntil d hdD) := by
    rw [SimpleGraph.Walk.takeUntil_append_of_mem_left]
    exact htakePD
  change S.support.idxOf d ≤ S.support.idxOf w
  have hwS : w ∈ S.support := by simpa [w] using hcollar
  by_contra hnot
  have hwd : S.support.idxOf w ≤ S.support.idxOf d := by omega
  have hwPrefix : w ∈ (S.takeUntil d hdS).support :=
    (rlc_mem_takeUntil_iff_idxOf_le S hdS hwS).2 hwd
  have hwPrefix' : w ∈ (P.append (D.takeUntil d hdD)).support := by
    have hwPrefix'' : w ∈
        (((P.append D).append Q).takeUntil d hdS').support := by
      simpa only [S] using hwPrefix
    simpa only [htakeS] using hwPrefix''
  rw [SimpleGraph.Walk.mem_support_append_iff] at hwPrefix'
  rcases hwPrefix' with hwP | hwDprefix
  · have hwWR := WR.support_dropUntil_subset hrWR hwP
    have hwPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 w).1 hwWR
    have hwBox := rlc_pathVertex_mem_rect gamma.1 hwPath
    rw [mem_rect] at hwBox
    dsimp only [w] at hwBox
    simp only [Matrix.cons_val_zero] at hwBox
    omega
  · have hw0 := rlc_bookExteriorEndpointDetour_takeUntil_topRight
      gamma gamma' w hwDprefix
    dsimp only [w] at hw0
    simp only [Matrix.cons_val_zero] at hw0
    omega

theorem rlc_bookRowOnePhysicalTraceNetworkBracket_collar_index_ge_exterior
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z : Site 2} (hzRight : z ∈ rlc_pathVertices gamma.1) {j : Nat}
    (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).length)
    (hjCollar : (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).getVert j = rlc_dualReflect.symm
        (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) :
    (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support.idxOf
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) ≤ j := by
  let hsLeft := rlc_bookRowOne_flippedLeftEndpoint_mem gamma'
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hzRight hsLeft
  let P := rlc_bookSimplePhysicalTraceNetworkBracket
    gamma gamma' hzRight hsLeft
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight
  let d : Site 2 := ![2 * n + 2, n + 2]
  let w : Site 2 := ![-2 * n - 1, (gamma'.1.1 : Site 2) 1]
  have hBSupport : B.support = P.support := by
    simp only [B, P, rlc_bookRowOnePhysicalTraceNetworkBracket,
      SimpleGraph.Walk.support_copy]
  have hBLength : B.length = P.length := by
    simp only [B, P, rlc_bookRowOnePhysicalTraceNetworkBracket,
      SimpleGraph.Walk.length_copy]
  have hBGet : B.getVert j = P.getVert j := by
    simp only [B, P, rlc_bookRowOnePhysicalTraceNetworkBracket,
      SimpleGraph.Walk.getVert_copy]
  have hPS : P = S.map rlc_dualReflectSymmLatticeHom := rfl
  have hgetMap : P.getVert j = rlc_dualReflect.symm (S.getVert j) := by
    rw [hPS]
    exact SimpleGraph.Walk.getVert_map rlc_dualReflectSymmLatticeHom S j
  have hjSource : S.getVert j = w := by
    apply rlc_dualReflect.symm.injective
    calc
      rlc_dualReflect.symm (S.getVert j) = P.getVert j := hgetMap.symm
      _ = B.getVert j := hBGet.symm
      _ = rlc_dualReflect.symm w := hjCollar
  have hwS : w ∈ S.support := by
    rw [← hjSource]
    exact S.getVert_mem_support j
  have hidxSource :=
    rlc_bookSimpleTraceNetworkBracket_collar_index_ge_exterior
      hn hzRight hsLeft hwS
  have hidxMap (x : Site 2) :
      P.support.idxOf (rlc_dualReflect.symm x) = S.support.idxOf x := by
    rw [hPS]
    have hsupp : (S.map rlc_dualReflectSymmLatticeHom).support =
        S.support.map rlc_dualReflect.symm :=
      SimpleGraph.Walk.support_map rlc_dualReflectSymmLatticeHom S
    calc
      (S.map rlc_dualReflectSymmLatticeHom).support.idxOf
          (rlc_dualReflect.symm x) =
          (S.support.map rlc_dualReflect.symm).idxOf
            (rlc_dualReflect.symm x) :=
        congrArg (fun l => l.idxOf (rlc_dualReflect.symm x)) hsupp
      _ = S.support.idxOf x := rlc_list_idxOf_map_of_injective _
        rlc_dualReflect.symm.injective _ _
  have hPPath := rlc_bookSimplePhysicalTraceNetworkBracket_isPath
    hn hfaith hzRight hsLeft
  have hidxJ : P.support.idxOf (P.getVert j) = j :=
    rlc_isPath_idxOf_getVert P hPPath j (by
      rw [← hBLength]
      exact hjLength)
  change B.support.idxOf (rlc_dualReflect.symm d) ≤ j
  calc
    B.support.idxOf (rlc_dualReflect.symm d) =
        P.support.idxOf (rlc_dualReflect.symm d) := by rw [hBSupport]
    _ = S.support.idxOf d := hidxMap _
    _ ≤ S.support.idxOf w := hidxSource
    _ = S.support.idxOf (S.getVert j) := congrArg S.support.idxOf hjSource.symm
    _ = P.support.idxOf (rlc_dualReflect.symm (S.getVert j)) :=
      (hidxMap _).symm
    _ = P.support.idxOf (P.getVert j) :=
      congrArg P.support.idxOf hgetMap.symm
    _ = j := hidxJ


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_mem_rect
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {z v : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hv : v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support) :
    v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1) := by
  simp only [rlc_bookRowOnePhysicalTraceNetworkBracket,
    SimpleGraph.Walk.support_copy,
    rlc_bookSimplePhysicalTraceNetworkBracket] at hv
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hzRight
    (s := rlc_flipX (gamma'.1.2.1 : Site 2))
      (rlc_bookRowOne_flippedLeftEndpoint_mem gamma')
  change v ∈ (S.map rlc_dualReflectSymmLatticeHom).support at hv
  rw [SimpleGraph.Walk.support_map rlc_dualReflectSymmLatticeHom S,
    List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  change rlc_dualReflect.symm w ∈
    rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1)
  dsimp only [S, rlc_bookSimpleTraceNetworkBracket] at hw
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with (hwRight | hwDetour) | hwLeft
  · have hwAmbient :=
      (rlc_ambientCrossingWalk gamma.1).support_dropUntil_subset
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma.1 z).2 hzRight) hwRight
    have hwPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 w).1
        hwAmbient
    have hwBox := rlc_pathVertex_mem_rect gamma.1 hwPath
    rw [mem_rect] at hwBox ⊢
    simp only [rlc_dualReflect_symm_zero, rlc_dualReflect_symm_one]
    omega
  · have hwBox : w ∈ rect (-2 * n - 2) (2 * n + 2) (-n) (n + 2) :=
      rlc_bookExteriorEndpointDetour_mem_rect gamma gamma' hwDetour
    rw [mem_rect] at hwBox ⊢
    simp only [rlc_dualReflect_symm_zero, rlc_dualReflect_symm_one]
    omega
  · have hwAmbient :=
      (rlc_ambientCrossingWalk gamma'.1).support_takeUntil_subset_support
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1
          (rlc_flipX (rlc_flipX (gamma'.1.2.1 : Site 2)))).2
            (rlc_bookRowOne_flippedLeftEndpoint_mem gamma')) hwLeft
    have hwPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 w).1
        hwAmbient
    have hwBox := rlc_pathVertex_mem_rect gamma'.1 hwPath
    rw [mem_rect] at hwBox ⊢
    simp only [rlc_dualReflect_symm_zero, rlc_dualReflect_symm_one]
    omega


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {z v : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hvBracket : v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support)
    (hvBoundary : v ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨
      rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨
      v = rlc_dualReflect.symm
        (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
  apply rlc_bookSimplePhysicalTraceNetworkBracket_boundaryContact_provenance
    hn gamma gamma' omega hzRight
      (rlc_bookRowOne_flippedLeftEndpoint_mem gamma')
  · simpa only [rlc_bookRowOnePhysicalTraceNetworkBracket,
      SimpleGraph.Walk.support_copy] using hvBracket
  · exact hvBoundary


theorem rlc_cycleVertex_mem_graphSupport
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (c : G.Walk u u) (hcycle : c.IsCycle) (hv : v ∈ c.support) :
    v ∈ G.support := by
  have hcNotNil : ¬c.Nil := by
    intro hnil
    exact hcycle.ne_nil hnil.eq_nil
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hcNotNil]
    at hv
  obtain ⟨e, he, hve⟩ := hv
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab := c.adj_of_mem_edges he
      rw [Sym2.mem_iff] at hve
      rcases hve with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab.mem_support_left
      · exact hab.mem_support_right


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_beforeExterior_boundaryContact
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'} {z u : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) {i : Nat}
    (hiLength : i ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).length)
    (hik : i < (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support.idxOf
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)))
    (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).getVert i ∈ c.support) :
    rlc_dualReflect ((rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).getVert i) ∈ rlc_pathVertices gamma.1 := by
  have hiProv :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance
      hn gamma gamma' omega hzRight
        ((rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).getVert_mem_support i)
        (rlc_cycleVertex_mem_graphSupport c hcycle hi)
  rcases hiProv with hiRight | hiLeft | hiCollar
  · exact hiRight
  · have hki :=
      rlc_bookRowOnePhysicalTraceNetworkBracket_left_index_ge_exterior
        hn hfaith hzRight hiLength hiLeft
    omega
  · have hki :=
      rlc_bookRowOnePhysicalTraceNetworkBracket_collar_index_ge_exterior
        hn hfaith hzRight hiLength hiCollar
    omega


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_afterExterior_boundaryContact
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'} {z u : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) {j : Nat}
    (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).length)
    (hkj : (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support.idxOf
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) < j)
    (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).getVert j ∈ c.support) :
    rlc_dualReflect ((rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).getVert j) ∈ rlc_pathVertices gamma'.1 ∨
      (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert j = rlc_dualReflect.symm
          (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
  have hjProv :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance
      hn gamma gamma' omega hzRight
        ((rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).getVert_mem_support j)
        (rlc_cycleVertex_mem_graphSupport c hcycle hj)
  rcases hjProv with hjRight | hjLeft | hjCollar
  · have hjLe :=
      rlc_bookRowOnePhysicalTraceNetworkBracket_right_index_le_exterior
        hn hfaith hzRight hjLength hjRight
    omega
  · exact Or.inl hjLeft
  · exact Or.inr hjCollar


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_cycleEndpoint_provenance
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {z u v : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hvBracket : v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support)
    (hvCycle : v ∈ c.support) :
    rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨
      rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨
      v = rlc_dualReflect.symm
        (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
  exact rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance
    hn gamma gamma' omega hzRight hvBracket
      (rlc_cycleVertex_mem_graphSupport c hcycle hvCycle)


theorem rlc_twoChannelFullPhysical_cleanChord_insideOutside_endpoint_cases
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    p = a ∨ p = b ∨ q ∈ H.support ∨
      p ∈ c.support ∨ q ∈ c.support := by
  have hpInside : p ∈ jec_leftRegion (c.mapLe
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle]
    exact rlc_twoChannelFullReachSet_subset_filled
      gamma gamma' omega hpReach
  have hpChord (hpH : p ∈ H.support) : p = a ∨ p = b := by
    rcases hclean p hpH with hpa | hpb | hpOff
    · exact Or.inl hpa
    · exact Or.inr hpb
    · exact False.elim (hpOff.2 hpInside)
  rcases
      rlc_twoChannelFullPhysical_insideOutsideEdge_endpointContact_cases
        c hcycle ha hb H hpqAdj hpReach hqOut with
    (hpH | hqH | hpArc | hqArc) | (hpH | hqH | hpArc | hqArc)
  · exact (hpChord hpH).elim Or.inl (fun h ↦ Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inl hqH))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (rlc_orderedContourArc_support_subset c ha hb hpArc))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (rlc_orderedContourArc_support_subset c ha hb hqArc))))
  · exact (hpChord hpH).elim Or.inl (fun h ↦ Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inl hqH))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (rlc_complementaryContourArc_support_subset c ha hb hpArc))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (rlc_complementaryContourArc_support_subset c ha hb hqArc))))


theorem rlc_exteriorWalk_contactInterval_separatorCycles
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b d : Site 2}
    (c : G.Walk u u) (hcycle : c.IsCycle)
    (B : (hypercubicLattice 2).Walk a b) (hBPath : B.IsPath)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hdB : d ∈ B.support) (hdC : d ∉ c.support)
    (hdOutside : d ∉ jec_leftRegion (c.mapLe hG)) :
    ∃ (i j : Nat)
      (H : (hypercubicLattice 2).Walk (B.getVert i) (B.getVert j))
      (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support),
      H.IsPath ∧ d ∈ H.support ∧ d ∉ c.support ∧
        H.support ⊆ B.support ∧
        (∀ v ∈ H.support,
          v = B.getVert i ∨ v = B.getVert j ∨
            (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe hG))) ∧
        (H.append ((rlc_orderedContourArc c hi hj).mapLe hG).reverse).IsCycle ∧
        (H.append
          ((rlc_complementaryContourArc c hi hj).mapLe hG).reverse).IsCycle := by
  let k := B.support.idxOf d
  have hkLength : k ≤ B.length := by
    have hk := List.idxOf_lt_length_of_mem hdB
    rw [SimpleGraph.Walk.length_support] at hk
    omega
  have hkGet : B.getVert k = d := B.getVert_support_idxOf hdB
  obtain ⟨i, j, hik, hkj, hjLength, hiMap, hjMap, hbetweenMap⟩ :=
    rlc_walk_exists_contact_extrema_around_offSupport B (c.mapLe hG)
      hkLength
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using ha)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hb)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support, hkGet] using hdC)
  have hbetween : ∀ l : Nat, i < l → l < j →
      B.getVert l ∉ c.support := by
    intro l hil hlj
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using
      hbetweenMap l hil hlj
  have hside : ∀ l : Nat, i < l → l < j →
      B.getVert l ∉ jec_leftRegion (c.mapLe hG) :=
    rlc_walk_contactInterval_same_leftRegion_side B (c.mapLe hG)
      hik hkj hjLength (by
        intro l hil hlj
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using
          hbetween l hil hlj) (by simpa [hkGet] using hdOutside)
  have hi : B.getVert i ∈ c.support := by
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hiMap
  have hj : B.getVert j ∈ c.support := by
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hjMap
  have hiLength : i ≤ B.length := by omega
  have hij : i ≤ j := by omega
  let H := rlc_walkIndexInterval B i j hiLength hij hjLength
  have hHPath : H.IsPath := by
    dsimp only [H, rlc_walkIndexInterval]
    simpa only [SimpleGraph.Walk.isPath_copy] using
      (hBPath.drop i).take (j - i)
  have hdH : d ∈ H.support := by
    have hkH := rlc_walkIndexInterval_getVert_mem B i j hiLength hij
      hjLength (Nat.le_of_lt hik) (Nat.le_of_lt hkj)
    simpa [hkGet] using hkH
  have hHB : H.support ⊆ B.support := by
    intro v hv
    obtain ⟨l, _hil, _hlj, hlv⟩ :=
      rlc_walkIndexInterval_support B i j hiLength hij hjLength hv
    rw [← hlv]
    exact B.getVert_mem_support l
  have hclean : ∀ v ∈ H.support,
      v = B.getVert i ∨ v = B.getVert j ∨
        (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe hG)) := by
    intro v hv
    by_cases hvi : v = B.getVert i
    · exact Or.inl hvi
    by_cases hvj : v = B.getVert j
    · exact Or.inr (Or.inl hvj)
    obtain ⟨l, hil, hlj, hlv⟩ :=
      rlc_walkIndexInterval_support_interior B i j hiLength hij hjLength
        hv hvi hvj
    exact Or.inr (Or.inr (by
      rw [← hlv]
      exact ⟨hbetween l hil hlj, hside l hil hlj⟩))
  have hcycles := rlc_exteriorChord_complementaryArcCycles hG c hcycle
    H hHPath hi hj hdH hdC (by
      intro v hv
      rcases hclean v hv with hvi | hvj | hoff
      · exact Or.inl hvi
      · exact Or.inr (Or.inl hvj)
      · exact Or.inr (Or.inr hoff.1))
  exact ⟨i, j, H, hi, hj, hHPath, hdH, hdC, hHB, hclean,
    hcycles.1, hcycles.2⟩


theorem rlc_walk_mem_indexInterval_or_before_or_after
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (B : G.Walk a b)
    (i j : Nat) (hiLength : i ≤ B.length) (hij : i ≤ j)
    (hjLength : j ≤ B.length) {z : V} (hz : z ∈ B.support) :
    z ∈ (rlc_walkIndexInterval B i j hiLength hij hjLength).support ∨
      (∃ k : Nat, k < i ∧ B.getVert k = z) ∨
      ∃ k : Nat, j < k ∧ k ≤ B.length ∧ B.getVert k = z := by
  let k := B.support.idxOf z
  have hkLength : k ≤ B.length := by
    have hk := List.idxOf_lt_length_of_mem hz
    rw [SimpleGraph.Walk.length_support] at hk
    omega
  have hkGet : B.getVert k = z := B.getVert_support_idxOf hz
  by_cases hki : k < i
  · exact Or.inr (Or.inl ⟨k, hki, hkGet⟩)
  by_cases hjk : j < k
  · exact Or.inr (Or.inr ⟨k, hjk, hkLength, hkGet⟩)
  left
  rw [← hkGet]
  exact rlc_walkIndexInterval_getVert_mem B i j hiLength hij hjLength
    (by omega) (by omega)

theorem rlc_exteriorBracket_contact_localized_to_indexInterval
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (B : G.Walk a b) (i j : Nat) (hiLength : i ≤ B.length)
    (hij : i ≤ j) (hjLength : j ≤ B.length)
    (P : V → Prop) (A : List V)
    (hcontact : (∃ z ∈ B.support, P z) ∨ ∃ z ∈ A, P z) :
    (∃ z ∈ (rlc_walkIndexInterval B i j hiLength hij hjLength).support,
        P z) ∨
      (∃ k : Nat, k < i ∧ P (B.getVert k)) ∨
      (∃ k : Nat, j < k ∧ k ≤ B.length ∧ P (B.getVert k)) ∨
      ∃ z ∈ A, P z := by
  rcases hcontact with ⟨z, hzB, hzP⟩ | hA
  · rcases rlc_walk_mem_indexInterval_or_before_or_after
      B i j hiLength hij hjLength hzB with hzH | ⟨k, hki, hkz⟩ |
        ⟨k, hjk, hkLength, hkz⟩
    · exact Or.inl ⟨z, hzH, hzP⟩
    · exact Or.inr (Or.inl ⟨k, hki, hkz ▸ hzP⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨k, hjk, hkLength, hkz ▸ hzP⟩))
  · exact Or.inr (Or.inr (Or.inr hA))


theorem rlc_exteriorWalk_contactInterval_separatorCycles_indexed
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b d : Site 2}
    (c : G.Walk u u) (hcycle : c.IsCycle)
    (B : (hypercubicLattice 2).Walk a b) (hBPath : B.IsPath)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hdB : d ∈ B.support) (hdC : d ∉ c.support)
    (hdOutside : d ∉ jec_leftRegion (c.mapLe hG)) :
    ∃ (i j : Nat) (hiLength : i ≤ B.length) (hij : i ≤ j)
      (hjLength : j ≤ B.length)
      (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support),
      let H := rlc_walkIndexInterval B i j hiLength hij hjLength
      i < B.support.idxOf d ∧ B.support.idxOf d < j ∧
        H.IsPath ∧ d ∈ H.support ∧ d ∉ c.support ∧
        H.support ⊆ B.support ∧
        (∀ v ∈ H.support,
          v = B.getVert i ∨ v = B.getVert j ∨
            (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe hG))) ∧
        (H.append
          ((rlc_orderedContourArc c hi hj).mapLe hG).reverse).IsCycle ∧
        (H.append
          ((rlc_complementaryContourArc c hi hj).mapLe hG).reverse).IsCycle := by
  let k := B.support.idxOf d
  have hkLength : k ≤ B.length := by
    have hk := List.idxOf_lt_length_of_mem hdB
    rw [SimpleGraph.Walk.length_support] at hk
    omega
  have hkGet : B.getVert k = d := B.getVert_support_idxOf hdB
  obtain ⟨i, j, hik, hkj, hjLength, hiMap, hjMap, hbetweenMap⟩ :=
    rlc_walk_exists_contact_extrema_around_offSupport B (c.mapLe hG)
      hkLength
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using ha)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hb)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support, hkGet] using hdC)
  have hbetween : ∀ l : Nat, i < l → l < j →
      B.getVert l ∉ c.support := by
    intro l hil hlj
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using
      hbetweenMap l hil hlj
  have hside : ∀ l : Nat, i < l → l < j →
      B.getVert l ∉ jec_leftRegion (c.mapLe hG) :=
    rlc_walk_contactInterval_same_leftRegion_side B (c.mapLe hG)
      hik hkj hjLength (by
        intro l hil hlj
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using
          hbetween l hil hlj) (by simpa [hkGet] using hdOutside)
  have hi : B.getVert i ∈ c.support := by
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hiMap
  have hj : B.getVert j ∈ c.support := by
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hjMap
  have hiLength : i ≤ B.length := by omega
  have hij : i ≤ j := by omega
  let H := rlc_walkIndexInterval B i j hiLength hij hjLength
  have hHPath : H.IsPath := by
    dsimp only [H, rlc_walkIndexInterval]
    simpa only [SimpleGraph.Walk.isPath_copy] using
      (hBPath.drop i).take (j - i)
  have hdH : d ∈ H.support := by
    have hkH := rlc_walkIndexInterval_getVert_mem B i j hiLength hij
      hjLength (Nat.le_of_lt hik) (Nat.le_of_lt hkj)
    simpa [hkGet] using hkH
  have hHB : H.support ⊆ B.support := by
    intro v hv
    obtain ⟨l, _hil, _hlj, hlv⟩ :=
      rlc_walkIndexInterval_support B i j hiLength hij hjLength hv
    rw [← hlv]
    exact B.getVert_mem_support l
  have hclean : ∀ v ∈ H.support,
      v = B.getVert i ∨ v = B.getVert j ∨
        (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe hG)) := by
    intro v hv
    by_cases hvi : v = B.getVert i
    · exact Or.inl hvi
    by_cases hvj : v = B.getVert j
    · exact Or.inr (Or.inl hvj)
    obtain ⟨l, hil, hlj, hlv⟩ :=
      rlc_walkIndexInterval_support_interior B i j hiLength hij hjLength
        hv hvi hvj
    exact Or.inr (Or.inr (by
      rw [← hlv]
      exact ⟨hbetween l hil hlj, hside l hil hlj⟩))
  have hcycles := rlc_exteriorChord_complementaryArcCycles hG c hcycle
    H hHPath hi hj hdH hdC (by
      intro v hv
      rcases hclean v hv with hvi | hvj | hoff
      · exact Or.inl hvi
      · exact Or.inr (Or.inl hvj)
      · exact Or.inr (Or.inr hoff.1))
  refine ⟨i, j, hiLength, hij, hjLength, hi, hj, ?_⟩
  dsimp only
  exact ⟨hik, hkj, hHPath, hdH, hdC, hHB, hclean,
    hcycles.1, hcycles.2⟩


theorem rlc_exteriorWalk_exteriorContact_reselect_separatorCycles_indexed
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b s t z : Site 2}
    (c : G.Walk u u) (hcycle : c.IsCycle)
    (B : (hypercubicLattice 2).Walk a b) (hBPath : B.IsPath)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (W : (hypercubicLattice 2).Walk s t)
    (hzW : z ∈ W.support) (hzB : z ∈ B.support)
    (hzC : z ∉ c.support)
    (hzOutside : z ∉ jec_leftRegion (c.mapLe hG)) :
    ∃ (i j : Nat) (hiLength : i ≤ B.length) (hij : i ≤ j)
      (hjLength : j ≤ B.length)
      (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support),
      let H := rlc_walkIndexInterval B i j hiLength hij hjLength
      H.IsPath ∧ z ∈ W.support ∧ z ∈ H.support ∧
        H.support ⊆ B.support ∧
        (∀ v ∈ H.support,
          v = B.getVert i ∨ v = B.getVert j ∨
            (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe hG))) ∧
        (H.append
          ((rlc_orderedContourArc c hi hj).mapLe hG).reverse).IsCycle ∧
        (H.append
          ((rlc_complementaryContourArc c hi hj).mapLe hG).reverse).IsCycle := by
  obtain ⟨i, j, hiLength, hij, hjLength, hi, hj, _hik, _hkj,
      hHPath, hzH, _hzC, hHB, hclean, hordered, hcomplementary⟩ :=
    rlc_exteriorWalk_contactInterval_separatorCycles_indexed
      hG c hcycle B hBPath ha hb hzB hzC hzOutside
  exact ⟨i, j, hiLength, hij, hjLength, hi, hj, hHPath, hzW, hzH,
    hHB, hclean, hordered, hcomplementary⟩


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'} {z u : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hstart : rlc_dualReflect.symm z ∈ c.support)
    (hend : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) ∈ c.support) :
    let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight
    let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
    ∃ (i j : Nat)
      (H : (hypercubicLattice 2).Walk (B.getVert i) (B.getVert j))
      (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support),
      H.IsPath ∧ d ∈ H.support ∧ d ∉ c.support ∧
        H.support ⊆ B.support ∧
        (∀ v ∈ H.support,
          v = B.getVert i ∨ v = B.getVert j ∨
            (v ∉ c.support ∧
              v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
                (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧
        (H.append ((rlc_orderedContourArc c hi hj).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
        (H.append ((rlc_complementaryContourArc c hi hj).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle := by
  dsimp only
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight
  let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
  have hdB : d ∈ B.support :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_exteriorPoint_mem
      gamma gamma' hzRight
  have hdC : d ∉ c.support := by
    intro hdc
    have hdBox := rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox
      hn gamma gamma' omega c hcycle hdc
    rw [mem_rect] at hdBox
    dsimp only [d] at hdBox
    simp only [rlc_dualReflect_symm_zero, Matrix.cons_val_zero] at hdBox
    omega
  have hdOutside : d ∉ jec_leftRegion
      (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle]
    intro hdFilled
    have hdBox := rlc_twoChannelFullFilledReachSet_subset_connectorRect
      hn gamma gamma' omega hdFilled
    rw [mem_rect] at hdBox
    dsimp only [d] at hdBox
    simp only [rlc_dualReflect_symm_zero, Matrix.cons_val_zero] at hdBox
    omega
  exact rlc_exteriorWalk_contactInterval_separatorCycles
    (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
    c hcycle B
      (rlc_bookRowOnePhysicalTraceNetworkBracket_isPath
        hn hfaith hzRight)
      hstart hend hdB hdC hdOutside


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles_indexed_oriented
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'} {z u : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hstart : rlc_dualReflect.symm z ∈ c.support)
    (hend : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) ∈ c.support) :
    let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight
    let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
    ∃ (i j : Nat) (hiLength : i ≤ B.length) (hij : i ≤ j)
      (hjLength : j ≤ B.length)
      (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support),
      let H := rlc_walkIndexInterval B i j hiLength hij hjLength
      i < B.support.idxOf d ∧ B.support.idxOf d < j ∧
        H.IsPath ∧ d ∈ H.support ∧ d ∉ c.support ∧
        H.support ⊆ B.support ∧
        (∀ v ∈ H.support,
          v = B.getVert i ∨ v = B.getVert j ∨
            (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe
              (faceBoundaryGraph_le
                (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧
        (H.append ((rlc_orderedContourArc c hi hj).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
        (H.append ((rlc_complementaryContourArc c hi hj).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
        rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧
        (rlc_dualReflect (B.getVert j) ∈ rlc_pathVertices gamma'.1 ∨
          B.getVert j = rlc_dualReflect.symm
            (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) := by
  dsimp only
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight
  let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
  have hdB : d ∈ B.support :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_exteriorPoint_mem
      gamma gamma' hzRight
  have hdC : d ∉ c.support := by
    intro hdc
    have hdBox := rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox
      hn gamma gamma' omega c hcycle hdc
    rw [mem_rect] at hdBox
    dsimp only [d] at hdBox
    simp only [rlc_dualReflect_symm_zero, Matrix.cons_val_zero] at hdBox
    omega
  have hdOutside : d ∉ jec_leftRegion
      (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle]
    intro hdFilled
    have hdBox := rlc_twoChannelFullFilledReachSet_subset_connectorRect
      hn gamma gamma' omega hdFilled
    rw [mem_rect] at hdBox
    dsimp only [d] at hdBox
    simp only [rlc_dualReflect_symm_zero, Matrix.cons_val_zero] at hdBox
    omega
  obtain ⟨i, j, hiLength, hij, hjLength, hi, hj, hik, hkj,
      hHPath, hdH, _hdC, hHB, hclean, hordered, hcomplementary⟩ :=
    rlc_exteriorWalk_contactInterval_separatorCycles_indexed
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
      c hcycle B
        (rlc_bookRowOnePhysicalTraceNetworkBracket_isPath
          hn hfaith hzRight)
        hstart hend hdB hdC hdOutside
  have hiRight :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_beforeExterior_boundaryContact
      hn hfaith hzRight c hcycle hiLength hik hi
  have hjGood :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_afterExterior_boundaryContact
      hn hfaith hzRight c hcycle hjLength hkj hj
  exact ⟨i, j, hiLength, hij, hjLength, hi, hj, hik, hkj,
    hHPath, hdH, hdC, hHB, hclean, hordered, hcomplementary,
    hiRight, hjGood⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowOne_separatorSourceSplice
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u z x y ur vr ul vl : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hxz : rlc_dualReflect x = z)
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
    ∃ (T : (hypercubicLattice 2).Walk vr vl)
      (i j : Nat)
      (H : (hypercubicLattice 2).Walk
        ((rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).getVert i)
        ((rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).getVert j))
      (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert i ∈ c.support)
      (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert j ∈ c.support),
      (∀ v ∈ T.support,
        v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
          ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
            phb_doubleDualShift a = v) ∧
      ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
        ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧
      H.IsPath ∧
      rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈ H.support ∧
      rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∉ c.support ∧
      H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).support ∧
      (∀ v ∈ H.support,
        v = (rlc_bookRowOnePhysicalTraceNetworkBracket
            gamma gamma' hzRight).getVert i ∨
          v = (rlc_bookRowOnePhysicalTraceNetworkBracket
            gamma gamma' hzRight).getVert j ∨
          (v ∉ c.support ∧
            v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
              (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧
      (H.append ((rlc_orderedContourArc c hi hj).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
      (H.append ((rlc_complementaryContourArc c hi hj).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle := by
  obtain ⟨T, hTprov, horder⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice
      hnoGood hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv
  have hstart : rlc_dualReflect.symm z ∈ c.support := by
    rw [← hxz]
    simpa using hx
  have hend : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) ∈ c.support := by
    rw [← hyAxis]
    simpa using hy
  obtain ⟨i, j, H, hi, hj, hHPath, hdH, hdC, hHB, hclean,
      hordered, hcomplementary⟩ :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles
      hn hfaith hzRight c hcycle hstart hend
  exact ⟨T, i, j, H, hi, hj, hTprov, horder, hHPath, hdH, hdC,
    hHB, hclean, hordered, hcomplementary⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowOne_reflectedLeftTerminalInterval
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur ul : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul)) :
    ∃ R : (hypercubicLattice 2).Walk ur ul,
      ∀ v ∈ R.support,
        ∃ w ∈ rlc_pathVertices gamma'.1,
          phb_doubleDualShift w = v := by
  let W := (rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom
  have hurW : rlc_dualReflect ur ∈ W.support := by
    obtain ⟨w, hw, huw⟩ := hrow.2.1.2.1
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨w,
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 w).2 hw,
      huw.symm⟩
  have hulW : rlc_dualReflect ul ∈ W.support := by
    obtain ⟨w, hw, huw⟩ := hrow.2.2.2.2.1
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨w,
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 w).2 hw,
      huw.symm⟩
  let i := W.support.idxOf (rlc_dualReflect ur)
  let j := W.support.idxOf (rlc_dualReflect ul)
  have hi : i ≤ W.length := by
    have h := List.idxOf_lt_length_of_mem hurW
    rw [SimpleGraph.Walk.length_support] at h
    omega
  have hj : j ≤ W.length := by
    have h := List.idxOf_lt_length_of_mem hulW
    rw [SimpleGraph.Walk.length_support] at h
    omega
  have hij : i ≤ j := by
    simpa [i, j, W] using horder.le
  let R0 := rlc_walkIndexInterval W i j hi hij hj
  have hR0Start : W.getVert i = rlc_dualReflect ur := by
    exact W.getVert_support_idxOf hurW
  have hR0End : W.getVert j = rlc_dualReflect ul := by
    exact W.getVert_support_idxOf hulW
  let R : (hypercubicLattice 2).Walk ur ul :=
    (R0.map rlc_dualReflectSymmLatticeHom).copy
      (by
        change rlc_dualReflect.symm (W.getVert i) = ur
        rw [hR0Start]
        exact rlc_dualReflect.symm_apply_apply ur)
      (by
        change rlc_dualReflect.symm (W.getVert j) = ul
        rw [hR0End]
        exact rlc_dualReflect.symm_apply_apply ul)
  refine ⟨R, ?_⟩
  intro v hv
  change v ∈ ((R0.map rlc_dualReflectSymmLatticeHom).copy _ _).support at hv
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
    List.mem_map] at hv
  obtain ⟨z, hzR0, rfl⟩ := hv
  obtain ⟨k, _hik, _hkj, hkz⟩ :=
    rlc_walkIndexInterval_support W i j hi hij hj hzR0
  have hzW : z ∈ W.support := by
    rw [← hkz]
    exact W.getVert_mem_support k
  dsimp only [W] at hzW
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hzW
  obtain ⟨w, hwW, hwz⟩ := hzW
  refine ⟨w,
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 w).1 hwW,
    ?_⟩
  rw [← hwz]
  simpa using
    (rlc_doubleDualShift_flipX_eq_dualReflect_symm (rlc_flipX w))


theorem rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl p q p' q' : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul)) :
    ∃ (Q : (hypercubicLattice 2).Walk q q')
      (W : (hypercubicLattice 2).Walk p p'),
      Q.support ⊆ W.support ∧
        (∀ z ∈ Q.support,
          z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
            z ∈ rlc_pathVertices gamma'.1) ∧
        ∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support := by
  obtain ⟨R, hR⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_reflectedLeftTerminalInterval
      hrow horder
  have hsharedR : sharedPrimalEdge vr ur = s(q, p) := by
    calc
      sharedPrimalEdge vr ur = sharedPrimalEdge ur vr :=
        (sharedPrimalEdge_comm_of_adj hurv).symm
      _ = s(p, q) := hpq
      _ = s(q, p) := Sym2.eq_swap
  have hsharedL : sharedPrimalEdge vl ul = s(q', p') := by
    calc
      sharedPrimalEdge vl ul = sharedPrimalEdge ul vl :=
        (sharedPrimalEdge_comm_of_adj hulv).symm
      _ = s(p', q') := hpq'
      _ = s(q', p') := Sym2.eq_swap
  obtain ⟨PR, hPR⟩ :=
    rlc_walk_secondFace_to_doubleDualShift_firstEndpoint
      hurv.symm hsharedR
  obtain ⟨PL, hPL⟩ :=
    rlc_walk_secondFace_to_doubleDualShift_firstEndpoint
      hulv.symm hsharedL
  let PR0 := PR.map rlc_doubleDualShiftSymmLatticeHom
  let PL0 := PL.map rlc_doubleDualShiftSymmLatticeHom
  let R0 := R.map rlc_doubleDualShiftSymmLatticeHom
  have hqEnd : phb_doubleDualEquiv.symm (phb_doubleDualShift q) = q :=
    phb_doubleDualEquiv.symm_apply_apply q
  have hqEnd' : phb_doubleDualEquiv.symm (phb_doubleDualShift q') = q' :=
    phb_doubleDualEquiv.symm_apply_apply q'
  let PR1 : (hypercubicLattice 2).Walk
      (phb_doubleDualEquiv.symm ur) q := PR0.copy rfl hqEnd
  let PL1 : (hypercubicLattice 2).Walk
      (phb_doubleDualEquiv.symm ul) q' := PL0.copy rfl hqEnd'
  let Q := (PR1.reverse.append R0).append PL1
  let W := (hpqAdj.toWalk.append Q).append hpqAdj'.symm.toWalk
  refine ⟨Q, W, ?_, ?_, ?_⟩
  · intro z hz
    dsimp only [W]
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inr hz)
  · intro z hz
    dsimp only [Q] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hzPR | hzR) | hzPL
    · dsimp only [PR1, PR0] at hzPR
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
        List.mem_map] at hzPR
      obtain ⟨v, hv, hvz⟩ := hzPR
      rcases hPR v hv with hvur | hvvr | hvq
      · obtain ⟨w, hw, huw⟩ := hrow.2.1.2.1
        right; right; right; right
        have hur : phb_doubleDualShift w = ur := by
          calc
            phb_doubleDualShift w =
                rlc_dualReflect.symm (rlc_flipX w) := by
              simpa using
                (rlc_doubleDualShift_flipX_eq_dualReflect_symm
                  (rlc_flipX w))
            _ = rlc_dualReflect.symm (rlc_dualReflect ur) := by rw [huw]
            _ = ur := rlc_dualReflect.symm_apply_apply ur
        have hzw : z = w := by
          rw [← hvz, hvur, ← hur]
          exact phb_doubleDualEquiv.symm_apply_apply w
        simpa [hzw] using hw
      · left
        rw [← hvz, hvvr, ← hpShift]
        exact phb_doubleDualEquiv.symm_apply_apply p
      · right; right; left
        rw [← hvz, hvq]
        exact phb_doubleDualEquiv.symm_apply_apply q
    · dsimp only [R0] at hzR
      have hsuppR : (R.map rlc_doubleDualShiftSymmLatticeHom).support =
          R.support.map rlc_doubleDualShiftSymmLatticeHom :=
        SimpleGraph.Walk.support_map rlc_doubleDualShiftSymmLatticeHom R
      have hzR' : z ∈ R.support.map
          rlc_doubleDualShiftSymmLatticeHom :=
        (congrArg (fun l => z ∈ l) hsuppR).mp hzR
      rw [List.mem_map] at hzR'
      obtain ⟨v, hv, hvz⟩ := hzR'
      obtain ⟨w, hw, hwv⟩ := hR v hv
      right; right; right; right
      have hzw : z = w := by
        rw [← hvz, ← hwv]
        exact phb_doubleDualEquiv.symm_apply_apply w
      simpa [hzw] using hw
    · dsimp only [PL1] at hzPL
      change z ∈ (PL0.copy _ _).support at hzPL
      rw [SimpleGraph.Walk.support_copy PL0] at hzPL
      have hzPL0 : z ∈ PL0.support := hzPL
      have hzPL' : z ∈ List.map
          rlc_doubleDualShiftSymmLatticeHom PL.support := by
        simpa only [PL0, SimpleGraph.Walk.support_map] using hzPL0
      rw [List.mem_map] at hzPL'
      obtain ⟨v, hv, hvz⟩ := hzPL'
      rcases hPL v hv with hvul | hvvl | hvq'
      · obtain ⟨w, hw, huw⟩ := hrow.2.2.2.2.1
        right; right; right; right
        have hul : phb_doubleDualShift w = ul := by
          calc
            phb_doubleDualShift w =
                rlc_dualReflect.symm (rlc_flipX w) := by
              simpa using
                (rlc_doubleDualShift_flipX_eq_dualReflect_symm
                  (rlc_flipX w))
            _ = rlc_dualReflect.symm (rlc_dualReflect ul) := by rw [huw]
            _ = ul := rlc_dualReflect.symm_apply_apply ul
        have hzw : z = w := by
          rw [← hvz, hvul, ← hul]
          exact phb_doubleDualEquiv.symm_apply_apply w
        simpa [hzw] using hw
      · right; left
        rw [← hvz, hvvl, ← hpShift']
        exact phb_doubleDualEquiv.symm_apply_apply p'
      · right; right; right; left
        rw [← hvz, hvq']
        exact phb_doubleDualEquiv.symm_apply_apply q'
  · intro z hz
    dsimp only [W] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hzPre | hzQ) | hzPost
    · simp [SimpleGraph.Adj.toWalk] at hzPre
      exact hzPre.elim Or.inl (fun h => Or.inr (Or.inr (h ▸ Q.start_mem_support)))
    · exact Or.inr (Or.inr hzQ)
    · simp [SimpleGraph.Adj.toWalk] at hzPost
      exact hzPost.elim
        (fun h => Or.inr (Or.inr (h ▸ Q.end_mem_support)))
        (fun h => Or.inr (Or.inl h))


theorem rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_cleanChord
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b x y ur vr ul vl p q p' q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hc : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ z ∈ H.support,
      z = a ∨ z = b ∨ (z ∉ c.support ∧
        z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
    (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
    (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
    (hLArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c ha hb).edges)
    (hcycles :
      (H.append ((rlc_orderedContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
      (H.append ((rlc_complementaryContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle)
    (havoid :
      (∀ z, (z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
          z ∈ rlc_pathVertices gamma'.1) →
        z ∉ (rlc_orderedContourArc c ha hb).support) ∨
      (∀ z, (z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
          z ∈ rlc_pathVertices gamma'.1) →
        z ∉ (rlc_complementaryContourArc c ha hb).support)) :
    ∃ z ∈ H.support,
      z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
        z ∈ rlc_pathVertices gamma'.1 := by
  obtain ⟨Q, W, hQW, hQprov, hWprov⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk
      hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder
  have hWclass : ∀ z ∈ W.support,
      z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
        z ∈ rlc_pathVertices gamma'.1 := by
    intro z hz
    rcases hWprov z hz with rfl | rfl | hzQ
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact hQprov z hzQ
  have hclean' : ∀ z ∈ H.support,
      z = a ∨ z = b ∨ z ∉ c.support := by
    intro z hz
    rcases hclean z hz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.1)
  have hRH : s(ur, vr) ∉ H.edges :=
    rlc_cleanChord_contourEdge_not_mem c H hclean'
      (rlc_orderedContourArc_edges_subset c ha hb hRArc)
        hterminalNe.1.1 hterminalNe.1.2
  have hLH : s(ul, vl) ∉ H.edges :=
    rlc_cleanChord_contourEdge_not_mem c H hclean'
      (rlc_complementaryContourArc_edges_subset c ha hb hLArc)
        hterminalNe.2.1 hterminalNe.2.2
  have hxor := rlc_exteriorChord_terminalEdges_closureXor_of_arcPlacement
    (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
    c hc.isTrail ha hb H hRArc hLArc hRH hLH
  have hselected :
      ((H.append ((rlc_orderedContourArc c ha hb).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
        ((s(ur, vr) ∈
              (H.append ((rlc_orderedContourArc c ha hb).mapLe
                (faceBoundaryGraph_le
                  (rlc_twoChannelFullFilledReachSet gamma gamma'
                    omega))).reverse).edges ∧
            s(ul, vl) ∉
              (H.append ((rlc_orderedContourArc c ha hb).mapLe
                (faceBoundaryGraph_le
                  (rlc_twoChannelFullFilledReachSet gamma gamma'
                    omega))).reverse).edges) ∨
          (s(ur, vr) ∉
              (H.append ((rlc_orderedContourArc c ha hb).mapLe
                (faceBoundaryGraph_le
                  (rlc_twoChannelFullFilledReachSet gamma gamma'
                    omega))).reverse).edges ∧
            s(ul, vl) ∈
              (H.append ((rlc_orderedContourArc c ha hb).mapLe
                (faceBoundaryGraph_le
                  (rlc_twoChannelFullFilledReachSet gamma gamma'
                    omega))).reverse).edges)) ∧
        ∀ z ∈ W.support,
          z ∉ (rlc_orderedContourArc c ha hb).support) ∨
      ((H.append ((rlc_complementaryContourArc c ha hb).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
        ((s(ur, vr) ∈
              (H.append ((rlc_complementaryContourArc c ha hb).mapLe
                (faceBoundaryGraph_le
                  (rlc_twoChannelFullFilledReachSet gamma gamma'
                    omega))).reverse).edges ∧
            s(ul, vl) ∉
              (H.append ((rlc_complementaryContourArc c ha hb).mapLe
                (faceBoundaryGraph_le
                  (rlc_twoChannelFullFilledReachSet gamma gamma'
                    omega))).reverse).edges) ∨
          (s(ur, vr) ∉
              (H.append ((rlc_complementaryContourArc c ha hb).mapLe
                (faceBoundaryGraph_le
                  (rlc_twoChannelFullFilledReachSet gamma gamma'
                    omega))).reverse).edges ∧
            s(ul, vl) ∈
              (H.append ((rlc_complementaryContourArc c ha hb).mapLe
                (faceBoundaryGraph_le
                  (rlc_twoChannelFullFilledReachSet gamma gamma'
                    omega))).reverse).edges)) ∧
        ∀ z ∈ W.support,
          z ∉ (rlc_complementaryContourArc c ha hb).support) := by
    rcases havoid with havoid | havoid
    · exact Or.inl ⟨hcycles.1, Or.inl hxor.1, fun z hz =>
        havoid z (hWclass z hz)⟩
    · exact Or.inr ⟨hcycles.2, Or.inr hxor.2, fun z hz =>
        havoid z (hWclass z hz)⟩
  obtain ⟨z, hzW, hzH⟩ :=
    rlc_exteriorChord_terminalFlankPath_meets_chord_of_closureEdgeXor
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
      c ha hb H hurv hulv hpqAdj hpqAdj' hpq hpq' Q W hQW hselected
  exact ⟨z, hzH, hWclass z hzW⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_meets_cleanChord_or_bothArcs
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b x y ur vr ul vl p q p' q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hc : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ z ∈ H.support,
      z = a ∨ z = b ∨ (z ∉ c.support ∧
        z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
    (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
    (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
    (hLArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c ha hb).edges)
    (hcycles :
      (H.append ((rlc_orderedContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
      (H.append ((rlc_complementaryContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle) :
    ∃ (Q : (hypercubicLattice 2).Walk q q')
      (W : (hypercubicLattice 2).Walk p p'),
      Q.support ⊆ W.support ∧
        (∀ z ∈ Q.support,
          z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
            z ∈ rlc_pathVertices gamma'.1) ∧
        (∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support) ∧
        ((∃ z ∈ W.support, z ∈ H.support) ∨
          ((∃ z ∈ W.support,
              z ∈ (rlc_orderedContourArc c ha hb).support) ∧
            ∃ z ∈ W.support,
              z ∈ (rlc_complementaryContourArc c ha hb).support)) := by
  obtain ⟨Q, W, hQW, hQprov, hWprov⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk
      hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder
  refine ⟨Q, W, hQW, hQprov, hWprov, ?_⟩
  have hclean' : ∀ z ∈ H.support,
      z = a ∨ z = b ∨ z ∉ c.support := by
    intro z hz
    rcases hclean z hz with hza | hzb | hzOff
    · exact Or.inl hza
    · exact Or.inr (Or.inl hzb)
    · exact Or.inr (Or.inr hzOff.1)
  have hRH : s(ur, vr) ∉ H.edges :=
    rlc_cleanChord_contourEdge_not_mem c H hclean'
      (rlc_orderedContourArc_edges_subset c ha hb hRArc)
        hterminalNe.1.1 hterminalNe.1.2
  have hLH : s(ul, vl) ∉ H.edges :=
    rlc_cleanChord_contourEdge_not_mem c H hclean'
      (rlc_complementaryContourArc_edges_subset c ha hb hLArc)
        hterminalNe.2.1 hterminalNe.2.2
  have hxor := rlc_exteriorChord_terminalEdges_closureXor_of_arcPlacement
    (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
    c hc.isTrail ha hb H hRArc hLArc hRH hLH
  by_cases hordered : ∃ z ∈ W.support,
      z ∈ (rlc_orderedContourArc c ha hb).support
  · by_cases hcomplementary : ∃ z ∈ W.support,
        z ∈ (rlc_complementaryContourArc c ha hb).support
    · exact Or.inr ⟨hordered, hcomplementary⟩
    · left
      obtain ⟨z, hzW, hzH⟩ :=
        rlc_exteriorChord_terminalFlankPath_meets_chord_of_closureEdgeXor
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
          c ha hb H hurv hulv hpqAdj hpqAdj' hpq hpq' Q W hQW
            (Or.inr ⟨hcycles.2, Or.inr hxor.2, by
              intro z hzW hzArc
              exact hcomplementary ⟨z, hzW, hzArc⟩⟩)
      exact ⟨z, hzW, hzH⟩
  · left
    obtain ⟨z, hzW, hzH⟩ :=
      rlc_exteriorChord_terminalFlankPath_meets_chord_of_closureEdgeXor
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
        c ha hb H hurv hulv hpqAdj hpqAdj' hpq hpq' Q W hQW
          (Or.inl ⟨hcycles.1, Or.inl hxor.1, by
            intro z hzW hzArc
            exact hordered ⟨z, hzW, hzArc⟩⟩)
    exact ⟨z, hzW, hzH⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_shiftWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl p q p' q' : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul)) :
    ∃ (Q : (hypercubicLattice 2).Walk q q')
      (W : (hypercubicLattice 2).Walk p p')
      (T : (hypercubicLattice 2).Walk vr vl),
      Q.support ⊆ W.support ∧
        (∀ z ∈ Q.support,
          z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
            z ∈ rlc_pathVertices gamma'.1) ∧
        (∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support) ∧
        (∀ z ∈ W.support, phb_doubleDualShift z ∈ T.support) ∧
        (∀ e ∈ W.edges, Sym2.map phb_doubleDualShift e ∈ T.edges) ∧
        (∀ e ∈ T.edges, ∃ e₀ ∈ W.edges,
          Sym2.map phb_doubleDualShift e₀ = e) ∧
        ∀ z ∈ T.support,
          z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
  obtain ⟨Q, W, hQW, hQprov, hWprov⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk
      hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder
  let hom : hypercubicLattice 2 →g hypercubicLattice 2 := {
    toFun := phb_doubleDualShift
    map_rel' := fun {_ _} h ↦ phb_doubleDualShift_latAdj.mpr h }
  let T : (hypercubicLattice 2).Walk vr vl :=
    (W.map hom).copy hpShift hpShift'
  have hWclass : ∀ z ∈ W.support,
      z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
        z ∈ rlc_pathVertices gamma'.1 := by
    intro z hz
    rcases hWprov z hz with rfl | rfl | hzQ
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact hQprov z hzQ
  refine ⟨Q, W, T, hQW, hQprov, hWprov, ?_, ?_, ?_, ?_⟩
  · intro z hz
    dsimp only [T]
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map]
    exact ⟨z, hz, rfl⟩
  · intro e he
    dsimp only [T]
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map,
      List.mem_map]
    exact ⟨e, he, rfl⟩
  · intro e he
    dsimp only [T] at he
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map,
      List.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    exact ⟨e₀, he₀, rfl⟩
  · intro z hz
    dsimp only [T] at hz
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    obtain ⟨r, hrW, rfl⟩ := hz
    change phb_doubleDualShift r ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)
    rcases hWclass r hrW with rfl | rfl | rfl | rfl | hrLeft
    · have hrBox := rlc_twoChannelFullReachSet_subset_box
        gamma gamma' omega hpReach
      have hshift := rlc_doubleDualShift_mem_translatedRect hrBox
      rw [mem_rect] at hshift ⊢
      omega
    · have hrBox := rlc_twoChannelFullReachSet_subset_box
        gamma gamma' omega hpReach'
      have hshift := rlc_doubleDualShift_mem_translatedRect hrBox
      rw [mem_rect] at hshift ⊢
      omega
    · have hpBox := rlc_twoChannelFullReachSet_subset_box
        gamma gamma' omega hpReach
      have hshift :=
        rlc_doubleDualShift_neighbor_mem_expandedRect hpBox hpqAdj
      rw [mem_rect] at hshift ⊢
      omega
    · have hpBox := rlc_twoChannelFullReachSet_subset_box
        gamma gamma' omega hpReach'
      have hshift :=
        rlc_doubleDualShift_neighbor_mem_expandedRect hpBox hpqAdj'
      rw [mem_rect] at hshift ⊢
      omega
    · have hrBox := rlc_pathVertex_mem_rect gamma'.1 hrLeft
      have hshift := rlc_doubleDualShift_mem_translatedRect hrBox
      rw [mem_rect] at hshift ⊢
      omega


theorem
    rlc_twoChannelFullPhysical_terminalPrimalFlank_meets_cleanChord_or_bothArcs
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b ur vr ul vl p q p' q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hc : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ z ∈ H.support,
      z = a ∨ z = b ∨ (z ∉ c.support ∧
        z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (Q : (hypercubicLattice 2).Walk q q')
    (W : (hypercubicLattice 2).Walk p p')
    (hQW : Q.support ⊆ W.support)
    (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
    (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
    (hLArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c ha hb).edges)
    (hcycles :
      (H.append ((rlc_orderedContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
      (H.append ((rlc_complementaryContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle) :
    (∃ z ∈ W.support, z ∈ H.support) ∨
      ((∃ z ∈ W.support,
          z ∈ (rlc_orderedContourArc c ha hb).support) ∧
        ∃ z ∈ W.support,
          z ∈ (rlc_complementaryContourArc c ha hb).support) := by
  have hclean' : ∀ z ∈ H.support,
      z = a ∨ z = b ∨ z ∉ c.support := by
    intro z hz
    rcases hclean z hz with hza | hzb | hzOff
    · exact Or.inl hza
    · exact Or.inr (Or.inl hzb)
    · exact Or.inr (Or.inr hzOff.1)
  have hRH : s(ur, vr) ∉ H.edges :=
    rlc_cleanChord_contourEdge_not_mem c H hclean'
      (rlc_orderedContourArc_edges_subset c ha hb hRArc)
        hterminalNe.1.1 hterminalNe.1.2
  have hLH : s(ul, vl) ∉ H.edges :=
    rlc_cleanChord_contourEdge_not_mem c H hclean'
      (rlc_complementaryContourArc_edges_subset c ha hb hLArc)
        hterminalNe.2.1 hterminalNe.2.2
  have hxor := rlc_exteriorChord_terminalEdges_closureXor_of_arcPlacement
    (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
    c hc.isTrail ha hb H hRArc hLArc hRH hLH
  by_cases hordered : ∃ z ∈ W.support,
      z ∈ (rlc_orderedContourArc c ha hb).support
  · by_cases hcomplementary : ∃ z ∈ W.support,
        z ∈ (rlc_complementaryContourArc c ha hb).support
    · exact Or.inr ⟨hordered, hcomplementary⟩
    · left
      exact rlc_exteriorChord_terminalFlankPath_meets_chord_of_closureEdgeXor
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
        c ha hb H hurv hulv hpqAdj hpqAdj' hpq hpq' Q W hQW
          (Or.inr ⟨hcycles.2, Or.inr hxor.2, by
            intro z hzW hzArc
            exact hcomplementary ⟨z, hzW, hzArc⟩⟩)
  · left
    exact rlc_exteriorChord_terminalFlankPath_meets_chord_of_closureEdgeXor
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
      c ha hb H hurv hulv hpqAdj hpqAdj' hpq hpq' Q W hQW
        (Or.inl ⟨hcycles.1, Or.inl hxor.1, by
          intro z hzW hzArc
          exact hordered ⟨z, hzW, hzArc⟩⟩)


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_BChanging
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {x y ur vr ul vl p q p' q' : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul)) :
    ∃ (Q : (hypercubicLattice 2).Walk q q')
      (W : (hypercubicLattice 2).Walk p p')
      (V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)))
      (f g : Site 2),
      Q.support ⊆ W.support ∧
        (∀ z ∈ Q.support,
          z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
            z ∈ rlc_pathVertices gamma'.1) ∧
        (∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support) ∧
        s(f, g) ∈ V.edges ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
        ((∃ e₀ ∈ W.edges,
            Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
          (s(f, g) = s(ur, vr) ∧
            RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
              gamma gamma' A B ur vr) ∨
          (s(f, g) = s(ul, vl) ∧
            RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
              gamma gamma' A B ul vl)) := by
  obtain ⟨Q, W, T, hQW, hQprov, hWprov, _hWT, _hWEdgeT,
      hTEdgeW, hTBox⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_shiftWalk
      hrow hurv.1 hulv.1 hpq hpq' hpqAdj hpqAdj' hpReach hpReach'
        hpShift hpShift' horder
  obtain ⟨V, f, g, hfgV, hcross, hlocation⟩ :=
    rlc_twoChannelFullPhysical_sourceSplice_BChanging_terminal_or_bridge
      hfaith A B hAright hAleft hBright hBleft hnoPair qr ql T hurv hulv
        hxPath hyPath hTBox
  have hterminal :=
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactTerminalResidue_or_bridge
      hn A B hAright hAleft hnoPair qr ql hrow hurv hulv hcross hlocation
  refine ⟨Q, W, V, f, g, hQW, hQprov, hWprov, hfgV, hcross, ?_⟩
  rcases hterminal with hbridge | hright | hleft
  · left
    exact hTEdgeW s(f, g) hbridge
  · exact Or.inr (Or.inl hright)
  · exact Or.inr (Or.inr hleft)


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_twoChannel
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u a b x y ur vr ul vl p q p' q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hc : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ z ∈ H.support,
      z = a ∨ z = b ∨ (z ∉ c.support ∧
        z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A))))))
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
    (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
    (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
    (hLArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c ha hb).edges)
    (hcycles :
      (H.append ((rlc_orderedContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A)))).reverse).IsCycle ∧
      (H.append ((rlc_complementaryContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A)))).reverse).IsCycle) :
    ∃ (Q : (hypercubicLattice 2).Walk q q')
      (W : (hypercubicLattice 2).Walk p p')
      (V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)))
      (f g : Site 2),
      Q.support ⊆ W.support ∧
        (∀ z ∈ Q.support,
          z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
            z ∈ rlc_pathVertices gamma'.1) ∧
        (∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support) ∧
        s(f, g) ∈ V.edges ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
        (((∃ e₀ ∈ W.edges,
              Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
            (s(f, g) = s(ur, vr) ∧
              RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
                gamma gamma' A B ur vr) ∨
            (s(f, g) = s(ul, vl) ∧
              RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
                gamma gamma' A B ul vl)) ∧
          ((∃ z ∈ W.support, z ∈ H.support) ∨
            ((∃ z ∈ W.support,
                z ∈ (rlc_orderedContourArc c ha hb).support) ∧
              ∃ z ∈ W.support,
                z ∈ (rlc_complementaryContourArc c ha hb).support))) := by
  obtain ⟨Q, W, V, f, g, hQW, hQprov, hWprov, hfgV, hcross,
      hchanging⟩ :=
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_BChanging
      hn hfaith A B hAright hAleft hBright hBleft hnoPair hxPath hyPath
        qr ql hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpReach hpReach'
          hpShift hpShift' horder
  have hcyclic :=
    rlc_twoChannelFullPhysical_terminalPrimalFlank_meets_cleanChord_or_bothArcs
      c hc ha hb H hclean hurv.1 hulv.1 hpq hpq' hpqAdj hpqAdj'
        Q W hQW hterminalNe hRArc hLArc hcycles
  exact ⟨Q, W, V, f, g, hQW, hQprov, hWprov, hfgV, hcross,
    hchanging, hcyclic⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_cleanChord_or_bothArcs
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b x y ur vr ul vl p q p' q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hc : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ z ∈ H.support,
      z = a ∨ z = b ∨ (z ∉ c.support ∧
        z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
    (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
    (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
    (hLArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c ha hb).edges)
    (hcycles :
      (H.append ((rlc_orderedContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
      (H.append ((rlc_complementaryContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle) :
    (∃ z ∈ H.support,
        z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
          z ∈ rlc_pathVertices gamma'.1) ∨
      ((∃ z ∈ (rlc_orderedContourArc c ha hb).support,
          z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
            z ∈ rlc_pathVertices gamma'.1) ∧
        ∃ z ∈ (rlc_complementaryContourArc c ha hb).support,
          z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
            z ∈ rlc_pathVertices gamma'.1) := by
  let P : Site 2 → Prop := fun z =>
    z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
      z ∈ rlc_pathVertices gamma'.1
  by_cases hordered : ∃ z ∈ (rlc_orderedContourArc c ha hb).support, P z
  · by_cases hcomplementary :
        ∃ z ∈ (rlc_complementaryContourArc c ha hb).support, P z
    · exact Or.inr ⟨hordered, hcomplementary⟩
    · left
      apply rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_cleanChord
        c hc ha hb H hclean hrow hurv hulv hpq hpq' hpqAdj hpqAdj'
          hpShift hpShift' horder hterminalNe hRArc hLArc hcycles
      right
      intro z hzP hzArc
      exact hcomplementary ⟨z, hzArc, hzP⟩
  · left
    apply rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_cleanChord
      c hc ha hb H hclean hrow hurv hulv hpq hpq' hpqAdj hpqAdj'
        hpShift hpShift' horder hterminalNe hRArc hLArc hcycles
    left
    intro z hzP hzArc
    exact hordered ⟨z, hzArc, hzP⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice_crosscut
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u z x y ur vr ul vl : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hxz : rlc_dualReflect x = z)
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
    (hdecR : rlc_orderedContourArc c hx hy =
      (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hurv rr))
    (hdecL : (rlc_complementaryContourArc c hx hy).reverse =
      (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hulv rl)) :
    ∃ T : (hypercubicLattice 2).Walk vr vl,
      (∀ v ∈ T.support,
        v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
          ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
            phb_doubleDualShift a = v) ∧
      ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
        ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧
      ((∃ v ∈ T.support,
          v ∈ (rlc_orderedContourArc c hx hy).support ∧
            v ∈ (rlc_complementaryContourArc c hx hy).support) ∨
        ∃ (i j : Nat) (hi : i ≤ T.length) (hij : i ≤ j)
            (hj : j ≤ T.length),
          i < j ∧
            T.getVert i ∈ (rlc_orderedContourArc c hx hy).support ∧
            T.getVert j ∈
              (rlc_complementaryContourArc c hx hy).support ∧
            ∀ v ∈ (rlc_walkIndexInterval T i j hi hij hj).support,
              v = T.getVert i ∨ v = T.getVert j ∨ v ∉ c.support) := by
  obtain ⟨T, hTprov, horder⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice
      hnoGood hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv
  have hurvArc : s(ur, vr) ∈
      (rlc_orderedContourArc c hx hy).edges := by
    rw [hdecR, SimpleGraph.Walk.edges_append]
    simp
  have hulvArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c hx hy).edges := by
    have hrev : s(ul, vl) ∈
        (rlc_complementaryContourArc c hx hy).reverse.edges := by
      rw [hdecL, SimpleGraph.Walk.edges_append]
      simp
    simpa [SimpleGraph.Walk.edges_reverse] using hrev
  have hvrArc : vr ∈ (rlc_orderedContourArc c hx hy).support :=
    (rlc_orderedContourArc c hx hy).snd_mem_support_of_mem_edges hurvArc
  have hvlArc : vl ∈
      (rlc_complementaryContourArc c hx hy).support :=
    (rlc_complementaryContourArc c hx hy).snd_mem_support_of_mem_edges
      hulvArc
  exact ⟨T, hTprov, horder,
    rlc_walk_ordered_to_complementary_crosscut
      c hx hy T hvrArc hvlArc⟩


theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminalReducedSourceResidue_separatorContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hres : RlcTwoChannelFullPhysicalReflectedLeftTerminalReducedSourceResidue
      gamma gamma' omega f g) :
    (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧
      ∃ p q : Site 2,
        sharedPrimalEdge f g = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
          ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
              gamma gamma' p ∧
            RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
              gamma gamma' omega p q) ∨
            p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧
          ((p ∈ H.support ∨ q ∈ H.support ∨
              p ∈ (rlc_orderedContourArc c ha hb).support ∨
              q ∈ (rlc_orderedContourArc c ha hb).support) ∨
            (p ∈ H.support ∨ q ∈ H.support ∨
              p ∈ (rlc_complementaryContourArc c ha hb).support ∨
              q ∈ (rlc_complementaryContourArc c ha hb).support)) := by
  rcases hres with
    ⟨hsourceBad, p, q, hpq, hpqAdj, hpReach, hqOut, hpPlace⟩
  refine ⟨hsourceBad, p, q, hpq, hpqAdj, hpReach, hqOut, hpPlace, ?_⟩
  exact rlc_twoChannelFullPhysical_insideOutsideEdge_endpointContact_cases
    c hcycle ha hb H hpqAdj hpReach hqOut


theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminalReducedSourceResidue_cleanSeparatorContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (hres : RlcTwoChannelFullPhysicalReflectedLeftTerminalReducedSourceResidue
      gamma gamma' omega f g) :
    (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧
      ∃ p q : Site 2,
        sharedPrimalEdge f g = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
          ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
              gamma gamma' p ∧
            RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
              gamma gamma' omega p q) ∨
            p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧
          (p = a ∨ p = b ∨ q ∈ H.support ∨
            p ∈ c.support ∨ q ∈ c.support) := by
  rcases hres with
    ⟨hsourceBad, p, q, hpq, hpqAdj, hpReach, hqOut, hpPlace⟩
  refine ⟨hsourceBad, p, q, hpq, hpqAdj, hpReach, hqOut, hpPlace, ?_⟩
  exact rlc_twoChannelFullPhysical_cleanChord_insideOutside_endpoint_cases
    c hcycle ha hb H hclean hpqAdj hpReach hqOut


theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminalExactResidue_cleanSeparatorContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    {u a b f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (hres : RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
      gamma gamma' A B f g) :
    ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_reflectedPathEdges gamma'.1) ∨
      ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
        target.1.map Subtype.val =
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
          rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
          (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
            gamma gamma' f g) ∧
          ∃ p q : Site 2,
            sharedPrimalEdge f g = s(p, q) ∧
              (hypercubicLattice 2).Adj p q ∧
              p ∈ rlc_twoChannelFullReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) ∧
              q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) ∧
              ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                  gamma gamma' p ∧
                RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
                  gamma gamma'
                    (rlc_twoChannelFullPhysicalCutInteriorConfig
                      gamma gamma' A) p q) ∨
                p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧
              (p = a ∨ p = b ∨ q ∈ H.support ∨
                p ∈ c.support ∨ q ∈ c.support) := by
  rcases hres with htarget | ⟨target, htarget, hcross, hsource⟩
  · exact Or.inl htarget
  · exact Or.inr ⟨target, htarget, hcross,
      rlc_twoChannelFullPhysical_reflectedLeftTerminalReducedSourceResidue_cleanSeparatorContact
        c hcycle ha hb H hclean hsource⟩


end
end StatMech.Universality
