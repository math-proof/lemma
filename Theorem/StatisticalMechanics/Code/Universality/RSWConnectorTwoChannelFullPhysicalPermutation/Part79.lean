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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part78
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_bookTraceNetworkBracket_eq_simple
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
    rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs =
      rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hrWR : r ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr
  have hsWR : s ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs
  have hsWL : rlc_flipX s ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft
  have hsSuffix : s ∈ (WR.dropUntil r hrWR).support :=
    (rlc_isPath_mem_dropUntil_iff_idxOf_le WR
      (rlc_ambientCrossingWalk_isPath gamma.1) hrWR hsWR).2 hrs
  have hnested : (WR.dropUntil r hrWR).dropUntil s hsSuffix =
      WR.dropUntil s hsWR :=
    rlc_isPath_dropUntil_dropUntil_eq WR
      (rlc_ambientCrossingWalk_isPath gamma.1) hrWR hsWR hrs hsSuffix
  let P := WR.dropUntil r hrWR
  let A := P.takeUntil s hsSuffix
  let R := WR.dropUntil s hsWR
  let D := rlc_bookExteriorEndpointDetour gamma gamma'
  let L := WL.takeUntil (rlc_flipX s) hsWL
  change A.append ((R.append D).append L) = (P.append D).append L
  have hR : R = P.dropUntil s hsSuffix := hnested.symm
  rw [hR, SimpleGraph.Walk.append_assoc,
    SimpleGraph.Walk.append_assoc, SimpleGraph.Walk.take_spec]


theorem rlc_bookPhysicalTraceNetworkBracket_eq_simple
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
    rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs =
      rlc_bookSimplePhysicalTraceNetworkBracket gamma gamma' hr hsLeft := by
  exact congrArg (fun W => W.map rlc_dualReflectSymmLatticeHom)
    (rlc_bookTraceNetworkBracket_eq_simple hr hs hsLeft hrs)


theorem rlc_bookSimpleTraceNetworkBracket_exteriorPoint_mem
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) :
    (![(2 * n + 2), n + 2] : Site 2) ∈
      (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hrWR : r ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr
  have hsWL : rlc_flipX s ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft
  change (![(2 * n + 2), n + 2] : Site 2) ∈
    (((WR.dropUntil r hrWR).append
      (rlc_bookExteriorEndpointDetour gamma gamma')).append
        (WL.takeUntil (rlc_flipX s) hsWL)).support
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl (Or.inr
    (rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'))


theorem rlc_bookSimpleTraceNetworkBracket_isPath {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) :
    (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).IsPath := by
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
  have hP : P.IsPath :=
    (rlc_ambientCrossingWalk_isPath gamma.1).dropUntil hrWR
  have hD : D.IsPath := rlc_bookExteriorEndpointDetour_isPath hn gamma gamma'
  have hQ : Q.IsPath :=
    (rlc_ambientCrossingWalk_isPath gamma'.1).takeUntil hsWL
  have hPD : (P.append D).IsPath := by
    apply rlc_append_isPath_of_endpoint_intersection hP hD
    intro v hvP hvD
    have hvWR := WR.support_dropUntil_subset hrWR hvP
    have hvRight :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 v).1 hvWR
    exact rlc_bookExteriorEndpointDetour_meets_rightBox_only_endpoint
      hn gamma gamma' hvD (rlc_pathVertex_mem_rect gamma.1 hvRight)
  have hPDQ : ((P.append D).append Q).IsPath := by
    apply rlc_append_isPath_of_endpoint_intersection hPD hQ
    intro v hvPD hvQ
    have hvWL := WL.support_takeUntil_subset_support hsWL hvQ
    have hvLeft :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 v).1 hvWL
    rw [SimpleGraph.Walk.mem_support_append_iff] at hvPD
    rcases hvPD with hvP | hvD
    · have hvWR := WR.support_dropUntil_subset hrWR hvP
      have hvRight :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 v).1 hvWR
      exact False.elim ((Finset.disjoint_left.mp hfaith.exposed_disjoint)
        hvRight hvLeft)
    · exact rlc_bookExteriorEndpointDetour_meets_leftBox_only_endpoint
        hn gamma gamma' hvD (rlc_pathVertex_mem_rect gamma'.1 hvLeft)
  simpa only [rlc_bookSimpleTraceNetworkBracket, P, D, Q, WR, WL] using hPDQ


theorem rlc_bookSimplePhysicalTraceNetworkBracket_isPath {n : Int}
    (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) :
    (rlc_bookSimplePhysicalTraceNetworkBracket
      gamma gamma' hr hsLeft).IsPath := by
  apply (rlc_bookSimpleTraceNetworkBracket
    gamma gamma' hr hsLeft).map_isPath_of_injective
  · exact rlc_dualReflect.symm.injective
  · exact rlc_bookSimpleTraceNetworkBracket_isPath
      hn hfaith hr hsLeft


theorem rlc_bookPhysicalTraceNetworkBracket_isPath
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
    (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).IsPath := by
  rw [rlc_bookPhysicalTraceNetworkBracket_eq_simple hr hs hsLeft hrs]
  exact rlc_bookSimplePhysicalTraceNetworkBracket_isPath
    hn hfaith hr hsLeft


theorem rlc_bookPhysicalTraceNetworkBracket_sameContact_isPath
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1) :
    (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hr hrLeft le_rfl).IsPath := by
  have hs := rlc_bookSimplePhysicalTraceNetworkBracket_isPath
    hn hfaith hr hrLeft
  simpa only [rlc_bookPhysicalTraceNetworkBracket,
    rlc_bookTraceNetworkBracket,
    rlc_rightAmbientTraceCanonicalSegment,
    rlc_bookOuterTraceNetworkArc,
    rlc_bookSimplePhysicalTraceNetworkBracket,
    rlc_bookSimpleTraceNetworkBracket,
    SimpleGraph.Walk.takeUntil_first,
    SimpleGraph.Walk.nil_append] using hs


theorem
    rlc_bookPhysicalTraceNetworkBracket_sameContact_right_index_le_exterior
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1)
    {j : Nat}
    (hjLength : j ≤ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hr hrLeft le_rfl).length)
    (hjRight : rlc_dualReflect
      ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hr hrLeft le_rfl).getVert j) ∈
          rlc_pathVertices gamma.1) :
    j ≤ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hr hrLeft le_rfl).support.idxOf
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) := by
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hrLeft
  let P := rlc_bookSimplePhysicalTraceNetworkBracket gamma gamma' hr hrLeft
  let B := rlc_bookPhysicalTraceNetworkBracket
    gamma gamma' hr hr hrLeft le_rfl
  let d : Site 2 := ![2 * n + 2, n + 2]
  have hBP : B = P := by
    simp only [B, P, rlc_bookPhysicalTraceNetworkBracket,
      rlc_bookTraceNetworkBracket,
      rlc_rightAmbientTraceCanonicalSegment,
      rlc_bookOuterTraceNetworkArc,
      rlc_bookSimplePhysicalTraceNetworkBracket,
      rlc_bookSimpleTraceNetworkBracket,
      SimpleGraph.Walk.takeUntil_first,
      SimpleGraph.Walk.nil_append]
  have hPS : P = S.map rlc_dualReflectSymmLatticeHom := rfl
  have hdS : d ∈ S.support := by
    exact rlc_bookSimpleTraceNetworkBracket_exteriorPoint_mem
      gamma gamma' hr hrLeft
  have hgetMap : P.getVert j = rlc_dualReflect.symm (S.getVert j) := by
    rw [hPS]
    exact SimpleGraph.Walk.getVert_map rlc_dualReflectSymmLatticeHom S j
  have hjSourceRight : S.getVert j ∈ rlc_pathVertices gamma.1 := by
    have hEq : rlc_dualReflect (B.getVert j) = S.getVert j := by
      calc
        _ = rlc_dualReflect (P.getVert j) := congrArg rlc_dualReflect
          (congrArg (fun W => W.getVert j) hBP)
        _ = rlc_dualReflect (rlc_dualReflect.symm (S.getVert j)) :=
          congrArg rlc_dualReflect hgetMap
        _ = _ := rlc_dualReflect.apply_symm_apply _
    exact hEq ▸ hjRight
  have hjS : S.getVert j ∈ S.support := S.getVert_mem_support j
  have hjPrefix : S.getVert j ∈ (S.takeUntil d hdS).support := by
    let WR := rlc_ambientCrossingWalk gamma.1
    let WL := rlc_ambientCrossingWalk gamma'.1
    have hrWR : r ∈ WR.support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr
    have hrWL : rlc_flipX r ∈ WL.support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (rlc_flipX r)).2 hrLeft
    let R := WR.dropUntil r hrWR
    let D := rlc_bookExteriorEndpointDetour gamma gamma'
    let L := WL.takeUntil (rlc_flipX r) hrWL
    have hdD : d ∈ D.support :=
      rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'
    have hdR : d ∉ R.support := by
      intro hdR
      have hdWR := WR.support_dropUntil_subset hrWR hdR
      have hdPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 d).1
          hdWR
      have hdBox := rlc_pathVertex_mem_rect gamma.1 hdPath
      rw [mem_rect] at hdBox
      simp [d] at hdBox
    have hdRD : d ∈ (R.append D).support :=
      SimpleGraph.Walk.subset_support_append_right R D hdD
    have htakeRD : (R.append D).takeUntil d hdRD =
        R.append (D.takeUntil d hdD) :=
      rlc_walk_takeUntil_append_of_notMem_left R D hdR hdD
    have htakeS : ((R.append D).append L).takeUntil d hdS =
        R.append (D.takeUntil d hdD) := by
      rw [SimpleGraph.Walk.takeUntil_append_of_mem_left]
      exact htakeRD
    have hjCases : S.getVert j ∈ R.support ∨
        S.getVert j ∈ D.support ∨ S.getVert j ∈ L.support := by
      change S.getVert j ∈ ((R.append D).append L).support at hjS
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.mem_support_append_iff] at hjS
      simpa [or_assoc] using hjS
    have hjR : S.getVert j ∈ R.support := by
      rcases hjCases with hjR | hjD | hjL
      · exact hjR
      · have hjEnd :=
          rlc_bookExteriorEndpointDetour_meets_rightBox_only_endpoint
            hn gamma gamma' hjD
              (rlc_pathVertex_mem_rect gamma.1 hjSourceRight)
        rw [hjEnd]
        exact R.end_mem_support
      · have hjWL := WL.support_takeUntil_subset_support hrWL hjL
        have hjLeft :=
          (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma'.1 (S.getVert j)).1 hjWL
        exact False.elim
          ((Finset.disjoint_left.mp hfaith.exposed_disjoint)
            hjSourceRight hjLeft)
    change S.getVert j ∈ (((R.append D).append L).takeUntil d hdS).support
    rw [htakeS, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hjR
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
    hn hfaith hr hrLeft
  have hidxJ : P.support.idxOf (P.getVert j) = j :=
    rlc_isPath_idxOf_getVert P hPPath j (by
      simpa [P, B, hBP] using hjLength)
  change j ≤ B.support.idxOf (rlc_dualReflect.symm d)
  calc
    j = P.support.idxOf (P.getVert j) := hidxJ.symm
    _ = P.support.idxOf (rlc_dualReflect.symm (S.getVert j)) :=
      congrArg P.support.idxOf hgetMap
    _ = S.support.idxOf (S.getVert j) := hidxMap _
    _ ≤ S.support.idxOf d := hidxSource
    _ = P.support.idxOf (rlc_dualReflect.symm d) := (hidxMap _).symm
    _ = B.support.idxOf (rlc_dualReflect.symm d) := by rw [hBP]


theorem rlc_bookSimpleTraceNetworkBracket_right_mem_exteriorPrefix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hn : 0 < n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s w : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hw : w ∈ (rlc_bookSimpleTraceNetworkBracket
      gamma gamma' hr hsLeft).support)
    (hwRight : w ∈ rlc_pathVertices gamma.1) :
    let d : Site 2 := ![2 * n + 2, n + 2]
    let W := rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft
    ∀ hd : d ∈ W.support, w ∈ (W.takeUntil d hd).support := by
  dsimp only
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
  let d : Site 2 := ![2 * n + 2, n + 2]
  have hdD : d ∈ D.support :=
    rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'
  have hdP : d ∉ P.support := by
    intro h
    have hdWR := WR.support_dropUntil_subset hrWR h
    have hdPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 d).1 hdWR
    have hdBox := rlc_pathVertex_mem_rect gamma.1 hdPath
    rw [mem_rect] at hdBox
    simp [d] at hdBox
  have hdPD : d ∈ (P.append D).support :=
    SimpleGraph.Walk.subset_support_append_right P D hdD
  intro hdW
  have htakePD : (P.append D).takeUntil d hdPD =
      P.append (D.takeUntil d hdD) :=
    rlc_walk_takeUntil_append_of_notMem_left P D hdP hdD
  have htakeW : ((P.append D).append Q).takeUntil d hdW =
      P.append (D.takeUntil d hdD) := by
    rw [SimpleGraph.Walk.takeUntil_append_of_mem_left]
    exact htakePD
  have hwCases : w ∈ P.support ∨ w ∈ D.support ∨ w ∈ Q.support := by
    change w ∈ ((P.append D).append Q).support at hw
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hw
    simpa [or_assoc] using hw
  have hwP : w ∈ P.support := by
    rcases hwCases with hwP | hwD | hwQ
    · exact hwP
    · have hwEnd :=
        rlc_bookExteriorEndpointDetour_meets_rightBox_only_endpoint
          hn gamma gamma' hwD
              (rlc_pathVertex_mem_rect gamma.1 hwRight)
      rw [hwEnd]
      exact P.end_mem_support
    · have hwWL := WL.support_takeUntil_subset_support hsWL hwQ
      have hwLeft :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 w).1
          hwWL
      exact False.elim ((Finset.disjoint_left.mp hfaith.exposed_disjoint)
        hwRight hwLeft)
  change w ∈ (((P.append D).append Q).takeUntil d hdW).support
  rw [htakeW, SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl hwP


theorem rlc_bookPhysicalTraceNetworkBracket_right_index_le_exterior
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    {j : Nat}
    (hjLength : j ≤ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).length)
    (hjRight : rlc_dualReflect
      ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert j) ∈
          rlc_pathVertices gamma.1) :
    j ≤ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support.idxOf
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) := by
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft
  let P := rlc_bookSimplePhysicalTraceNetworkBracket gamma gamma' hr hsLeft
  let B := rlc_bookPhysicalTraceNetworkBracket
    gamma gamma' hr hs hsLeft hrs
  let d : Site 2 := ![2 * n + 2, n + 2]
  have hBP : B = P :=
    rlc_bookPhysicalTraceNetworkBracket_eq_simple hr hs hsLeft hrs
  have hPS : P = S.map rlc_dualReflectSymmLatticeHom := rfl
  have hdS : d ∈ S.support :=
    rlc_bookSimpleTraceNetworkBracket_exteriorPoint_mem
      gamma gamma' hr hsLeft
  have hgetMap : P.getVert j = rlc_dualReflect.symm (S.getVert j) := by
    rw [hPS]
    exact SimpleGraph.Walk.getVert_map rlc_dualReflectSymmLatticeHom S j
  have hjSourceRight : S.getVert j ∈ rlc_pathVertices gamma.1 := by
    have hEq : rlc_dualReflect (B.getVert j) = S.getVert j := by
      calc
        _ = rlc_dualReflect (P.getVert j) := congrArg rlc_dualReflect
          (congrArg (fun W => W.getVert j) hBP)
        _ = rlc_dualReflect (rlc_dualReflect.symm (S.getVert j)) :=
          congrArg rlc_dualReflect hgetMap
        _ = _ := rlc_dualReflect.apply_symm_apply _
    exact hEq ▸ hjRight
  have hjS : S.getVert j ∈ S.support := S.getVert_mem_support j
  have hjPrefix : S.getVert j ∈ (S.takeUntil d hdS).support :=
    rlc_bookSimpleTraceNetworkBracket_right_mem_exteriorPrefix
      hn hfaith hr hsLeft hjS hjSourceRight hdS
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
    hn hfaith hr hsLeft
  have hidxJ : P.support.idxOf (P.getVert j) = j :=
    rlc_isPath_idxOf_getVert P hPPath j (by
      simpa [B, hBP] using hjLength)
  change j ≤ B.support.idxOf (rlc_dualReflect.symm d)
  calc
    j = P.support.idxOf (P.getVert j) := hidxJ.symm
    _ = P.support.idxOf (rlc_dualReflect.symm (S.getVert j)) :=
      congrArg P.support.idxOf hgetMap
    _ = S.support.idxOf (S.getVert j) := hidxMap _
    _ ≤ S.support.idxOf d := hidxSource
    _ = P.support.idxOf (rlc_dualReflect.symm d) := (hidxMap _).symm
    _ = B.support.idxOf (rlc_dualReflect.symm d) := by rw [hBP]


theorem
    rlc_bookPhysicalExteriorEndpointDetour_meets_filledBoundary_only_endpointCollar
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {v : Site 2}
    (hvDetour : v ∈ ((rlc_bookExteriorEndpointDetour gamma gamma').map
      rlc_dualReflectSymmLatticeHom).support)
    (hvBoundary : v ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    v = rlc_dualReflect.symm (gamma.1.2.1 : Site 2) ∨
      v = rlc_dualReflect.symm (gamma'.1.1 : Site 2) ∨
      v = rlc_dualReflect.symm
        (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hvDetour
  obtain ⟨w, hwDetour, rfl⟩ := hvDetour
  change rlc_dualReflect.symm w ∈ (faceBoundaryGraph
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support at hvBoundary
  change rlc_dualReflect.symm w =
      rlc_dualReflect.symm (gamma.1.2.1 : Site 2) ∨
    rlc_dualReflect.symm w =
      rlc_dualReflect.symm (gamma'.1.1 : Site 2) ∨
    rlc_dualReflect.symm w = rlc_dualReflect.symm
      (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)
  have hvBox := rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
    hn gamma gamma' omega hvBoundary
  have hr0 : (gamma.1.2.1 : Site 2) 0 = 2 * n := gamma.1.2.1.2.2
  have hl0 : (gamma'.1.1 : Site 2) 0 = -2 * n := gamma'.1.1.2.2
  rcases rlc_bookExteriorEndpointDetour_support_cases
      gamma gamma' hwDetour with hw | hw | hw | hw | hw
  · rw [sw_horizSeg_mem_support] at hw
    obtain ⟨t, ht, hwt⟩ := hw
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hvBox
    simp only [hwt, rlc_dualReflect_symm_zero,
      rlc_dualReflect_symm_one, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hvBox ⊢
    have htEq : t = 2 * n := by
      rcases ht with ht | ht <;> omega
    left
    rw [htEq]
    apply congrArg rlc_dualReflect.symm
    ext i
    fin_cases i <;> simp [hr0]
  · rw [sw_vertSeg_mem_support] at hw
    obtain ⟨t, _ht, hwt⟩ := hw
    rw [mem_rect] at hvBox
    simp only [hwt, rlc_dualReflect_symm_zero,
      Matrix.cons_val_zero] at hvBox
    omega
  · rw [sw_horizSeg_mem_support] at hw
    obtain ⟨t, _ht, hwt⟩ := hw
    rw [mem_rect] at hvBox
    simp [hwt, rlc_dualReflect, rlc_dualReflectInvFun] at hvBox
  · rw [sw_horizSeg_mem_support] at hw
    obtain ⟨t, ht, hwt⟩ := hw
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hvBox
    simp only [hwt, rlc_dualReflect_symm_zero,
      rlc_dualReflect_symm_one, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hvBox ⊢
    have htCases : t = -2 * n ∨ t = -2 * n - 1 := by
      rcases ht with ht | ht <;> omega
    rcases htCases with htEq | htEq
    · right; left
      rw [htEq]
      apply congrArg rlc_dualReflect.symm
      ext i
      fin_cases i <;> simp [hl0]
    · right; right
      rw [htEq]
  · rw [sw_vertSeg_mem_support] at hw
    obtain ⟨t, _ht, hwt⟩ := hw
    rw [mem_rect] at hvBox
    simp only [hwt, rlc_dualReflect_symm_zero,
      Matrix.cons_val_zero] at hvBox
    omega


theorem rlc_bookPhysicalRightEndpointLeg_meets_filledBoundary_only_endpoint
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {w : Site 2}
    (hw : w ∈ (sw_lshape ((gamma.1.2.1 : Site 2) 0)
      ((gamma.1.2.1 : Site 2) 1) (2 * n + 2) (n + 2)).support)
    (hwBoundary : rlc_dualReflect.symm w ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    w = (gamma.1.2.1 : Site 2) := by
  let rr : Site 2 := gamma.1.2.1
  let ll : Site 2 := gamma'.1.1
  have hrr : (![rr 0, rr 1] : Site 2) = rr := by
    ext i
    fin_cases i <;> simp
  have hll : (![ll 0, ll 1] : Site 2) = ll := by
    ext i
    fin_cases i <;> simp
  have hwDetour : w ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support := by
    change w ∈ (((
      (sw_lshape (rr 0) (rr 1) (2 * n + 2) (n + 2)).copy hrr rfl).append
        (sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2))).append
          (((sw_lshape (ll 0) (ll 1) (-2 * n - 2) (n + 2)).reverse).copy
            rfl hll)).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    left
    simpa only [rr, SimpleGraph.Walk.support_copy] using hw
  have hwMapped : rlc_dualReflect.symm w ∈
      ((rlc_bookExteriorEndpointDetour gamma gamma').map
        rlc_dualReflectSymmLatticeHom).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨w, hwDetour, rfl⟩
  rcases
      rlc_bookPhysicalExteriorEndpointDetour_meets_filledBoundary_only_endpointCollar
        hn gamma gamma' omega hwMapped hwBoundary with
    hwRight | hwLeft | hwCollar
  · exact rlc_dualReflect.symm.injective hwRight
  · have hwl : w = ll := rlc_dualReflect.symm.injective hwLeft
    have hr0 : rr 0 = 2 * n := gamma.1.2.1.2.2
    have hl0 : ll 0 = -2 * n := gamma'.1.1.2.2
    dsimp only [rr] at hr0
    dsimp only [ll] at hl0
    rw [sw_lshape_support_eq] at hw
    rcases hw with ⟨t, ht, hwt⟩ | ⟨t, ht, hwt⟩ <;>
      rw [Set.mem_uIcc] at ht <;>
      have h0 := congrArg (fun z : Site 2 => z 0) (hwt.symm.trans hwl) <;>
      dsimp only [rr, ll] at h0 <;>
      simp only [Matrix.cons_val_zero] at h0 <;> omega
  · have hwc : w =
        (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) :=
      rlc_dualReflect.symm.injective hwCollar
    have hr0 : rr 0 = 2 * n := gamma.1.2.1.2.2
    dsimp only [rr] at hr0
    rw [sw_lshape_support_eq] at hw
    rcases hw with ⟨t, ht, hwt⟩ | ⟨t, ht, hwt⟩ <;>
      rw [Set.mem_uIcc] at ht <;>
      have h0 := congrArg (fun z : Site 2 => z 0) (hwt.symm.trans hwc) <;>
      dsimp only [rr] at h0 <;>
      simp only [Matrix.cons_val_zero] at h0 <;> omega


theorem rlc_bookSimplePhysicalTraceNetworkBracket_boundaryContact_provenance
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hvBracket : v ∈ (rlc_bookSimplePhysicalTraceNetworkBracket
      gamma gamma' hr hsLeft).support)
    (hvBoundary : v ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨
      rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨
      v = rlc_dualReflect.symm
        (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
  change v ∈ ((rlc_bookSimpleTraceNetworkBracket
    gamma gamma' hr hsLeft).map
      rlc_dualReflectSymmLatticeHom).support at hvBracket
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hvBracket
  obtain ⟨w, hwBracket, hwv⟩ := hvBracket
  have hvw : v = rlc_dualReflect.symm w := hwv.symm
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hrWR : r ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr
  have hsWL : rlc_flipX s ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft
  change w ∈ (((WR.dropUntil r hrWR).append
    (rlc_bookExteriorEndpointDetour gamma gamma')).append
      (WL.takeUntil (rlc_flipX s) hsWL)).support at hwBracket
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hwBracket
  rcases hwBracket with (hwRight | hwDetour) | hwLeft
  · left
    rw [hvw, rlc_dualReflect.apply_symm_apply]
    have hwWR := WR.support_dropUntil_subset hrWR hwRight
    exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 w).1 hwWR
  · have hvDetour : v ∈
        ((rlc_bookExteriorEndpointDetour gamma gamma').map
          rlc_dualReflectSymmLatticeHom).support := by
      rw [SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨w, hwDetour, hwv⟩
    rcases
        rlc_bookPhysicalExteriorEndpointDetour_meets_filledBoundary_only_endpointCollar
          hn gamma gamma' omega hvDetour hvBoundary with
      hvRight | hvLeft | hvCollar
    · left
      rw [hvRight, rlc_dualReflect.apply_symm_apply]
      exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma.1 (gamma.1.2.1 : Site 2)).1
          (rlc_ambientCrossingWalk gamma.1).end_mem_support
    · right
      left
      rw [hvLeft, rlc_dualReflect.apply_symm_apply]
      exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (gamma'.1.1 : Site 2)).1
          (rlc_ambientCrossingWalk gamma'.1).start_mem_support
    · exact Or.inr (Or.inr hvCollar)
  · right
    left
    rw [hvw, rlc_dualReflect.apply_symm_apply]
    have hwWL := WL.support_takeUntil_subset_support hsWL hwLeft
    exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 w).1 hwWL


theorem rlc_bookExteriorEndpointDetour_meets_rightTrace_only_endpoint
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {v : Site 2}
    (hvDetour : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support)
    (hvRight : v ∈ rlc_pathVertices gamma.1) :
    v = (gamma.1.2.1 : Site 2) := by
  have hn : 0 < n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hstrict := hfaith.right_axis_strict
    omega
  have hvBox := rlc_pathVertex_mem_rect gamma.1 hvRight
  have hr0 : (gamma.1.2.1 : Site 2) 0 = 2 * n := gamma.1.2.1.2.2
  have hl0 : (gamma'.1.1 : Site 2) 0 = -2 * n := gamma'.1.1.2.2
  rcases rlc_bookExteriorEndpointDetour_support_cases
      gamma gamma' hvDetour with hv | hv | hv | hv | hv
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hvBox
    have htEq : t = 2 * n := by
      rcases ht with ht | ht <;> simp only [hvt, Matrix.cons_val_zero] at hvBox <;>
        omega
    rw [hvt, htEq]
    ext i
    fin_cases i <;> simp [hr0]
  · rw [sw_vertSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp only [hvt, Matrix.cons_val_zero] at hvBox
    omega
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp [hvt] at hvBox
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hvBox
    simp only [hvt, Matrix.cons_val_zero] at hvBox
    rcases ht with ht | ht <;> omega
  · rw [sw_vertSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp only [hvt, Matrix.cons_val_zero] at hvBox
    omega


theorem rlc_bookExteriorEndpointDetour_meets_leftTrace_only_endpoint
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {v : Site 2}
    (hvDetour : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support)
    (hvLeft : v ∈ rlc_pathVertices gamma'.1) :
    v = (gamma'.1.1 : Site 2) := by
  have hn : 0 < n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hstrict := hfaith.right_axis_strict
    omega
  have hvBox := rlc_pathVertex_mem_rect gamma'.1 hvLeft
  have hr0 : (gamma.1.2.1 : Site 2) 0 = 2 * n := gamma.1.2.1.2.2
  have hl0 : (gamma'.1.1 : Site 2) 0 = -2 * n := gamma'.1.1.2.2
  rcases rlc_bookExteriorEndpointDetour_support_cases
      gamma gamma' hvDetour with hv | hv | hv | hv | hv
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hvBox
    simp only [hvt, Matrix.cons_val_zero] at hvBox
    rcases ht with ht | ht <;> omega
  · rw [sw_vertSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp only [hvt, Matrix.cons_val_zero] at hvBox
    omega
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp [hvt] at hvBox
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hvBox
    have htEq : t = -2 * n := by
      rcases ht with ht | ht <;> simp only [hvt, Matrix.cons_val_zero] at hvBox <;>
        omega
    rw [hvt, htEq]
    ext i
    fin_cases i <;> simp [hl0]
  · rw [sw_vertSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp only [hvt, Matrix.cons_val_zero] at hvBox
    omega


theorem rlc_bookOuterTraceNetworkArc_support_cases {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {s v : Site 2}
    (hsRight : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hv : v ∈ (rlc_bookOuterTraceNetworkArc
      gamma gamma' hsRight hsLeft).support) :
    v ∈ ((rlc_ambientCrossingWalk gamma.1).dropUntil s
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma.1 s).2 hsRight)).support ∨
      v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support ∨
      v ∈ ((rlc_ambientCrossingWalk gamma'.1).takeUntil
        (rlc_flipX s)
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 (rlc_flipX s)).2 hsLeft)).support := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hsWR : s ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2
      hsRight
  have hsWL : rlc_flipX s ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft
  change v ∈ (((WR.dropUntil s hsWR).append
    (rlc_bookExteriorEndpointDetour gamma gamma')).append
      (WL.takeUntil (rlc_flipX s) hsWL)).support at hv
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hv
  simpa [WR, WL, or_assoc] using hv


theorem rlc_rightAmbientTraceCanonicalSegment_support_path {n : Int}
    (gamma : RlcRightDiagonalPath n) {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hv : v ∈ (rlc_rightAmbientTraceCanonicalSegment
      gamma hr hs hrs).support) :
    v ∈ rlc_pathVertices gamma.1 := by
  let W := rlc_ambientCrossingWalk gamma.1
  have hrW : r ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr
  have hsW : s ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs
  have hsSuffix : s ∈ (W.dropUntil r hrW).support :=
    (rlc_isPath_mem_dropUntil_iff_idxOf_le W
      (rlc_ambientCrossingWalk_isPath gamma.1) hrW hsW).2 hrs
  change v ∈ ((W.dropUntil r hrW).takeUntil s hsSuffix).support at hv
  have hvW := W.support_dropUntil_subset hrW
    ((W.dropUntil r hrW).support_takeUntil_subset_support hsSuffix hv)
  exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 v).1
    hvW


theorem rlc_bookPhysicalTraceNetworkBracket_boundaryContact_provenance
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hvBracket : v ∈ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support)
    (hvBoundary : v ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨
      rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨
      v = rlc_dualReflect.symm
        (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
  change v ∈ ((rlc_bookTraceNetworkBracket
    gamma gamma' hr hs hsLeft hrs).map
      rlc_dualReflectSymmLatticeHom).support at hvBracket
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hvBracket
  obtain ⟨w, hwBracket, hwv⟩ := hvBracket
  have hvw : v = rlc_dualReflect.symm w := hwv.symm
  change w ∈ ((rlc_rightAmbientTraceCanonicalSegment
    gamma hr hs hrs).append
      (rlc_bookOuterTraceNetworkArc gamma gamma' hs hsLeft)).support at hwBracket
  rw [SimpleGraph.Walk.mem_support_append_iff] at hwBracket
  rcases hwBracket with hwRight | hwOuter
  · left
    rw [hvw, rlc_dualReflect.apply_symm_apply]
    exact rlc_rightAmbientTraceCanonicalSegment_support_path
      gamma hr hs hrs hwRight
  · rcases rlc_bookOuterTraceNetworkArc_support_cases
        gamma gamma' hs hsLeft hwOuter with hwRight | hwDetour | hwLeft
    · left
      rw [hvw, rlc_dualReflect.apply_symm_apply]
      have hwAmbient :=
        (rlc_ambientCrossingWalk gamma.1).support_dropUntil_subset
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma.1 s).2 hs) hwRight
      exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma.1 w).1 hwAmbient
    · have hvDetour : v ∈
          ((rlc_bookExteriorEndpointDetour gamma gamma').map
            rlc_dualReflectSymmLatticeHom).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨w, hwDetour, hwv⟩
      rcases
          rlc_bookPhysicalExteriorEndpointDetour_meets_filledBoundary_only_endpointCollar
            hn gamma gamma' omega hvDetour hvBoundary with
        hvRight | hvLeft | hvCollar
      · left
        rw [hvRight, rlc_dualReflect.apply_symm_apply]
        exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma.1 (gamma.1.2.1 : Site 2)).1
            (rlc_ambientCrossingWalk gamma.1).end_mem_support
      · right; left
        rw [hvLeft, rlc_dualReflect.apply_symm_apply]
        exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 (gamma'.1.1 : Site 2)).1
            (rlc_ambientCrossingWalk gamma'.1).start_mem_support
      · exact Or.inr (Or.inr hvCollar)
    · right; left
      rw [hvw, rlc_dualReflect.apply_symm_apply]
      have hwAmbient :=
        (rlc_ambientCrossingWalk gamma'.1).support_takeUntil_subset_support
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma'.1 (rlc_flipX s)).2 hsLeft) hwLeft
      exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 w).1 hwAmbient


theorem rlc_bookTraceNetworkBracket_meets_rightPrefix_only_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hvBracket : v ∈ (rlc_bookTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support)
    (hvPrefix : v ∈ ((rlc_ambientCrossingWalk gamma.1).takeUntil r
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma.1 r).2 hr)).support) :
    v = r := by
  let WR := rlc_ambientCrossingWalk gamma.1
  have hrW : r ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr
  have hsW : s ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs
  change v ∈ ((rlc_rightAmbientTraceCanonicalSegment
    gamma hr hs hrs).append
      (rlc_bookOuterTraceNetworkArc gamma gamma' hs hsLeft)).support at hvBracket
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvBracket
  rcases hvBracket with hvSegment | hvOuter
  · exact rlc_rightAmbientTrace_prefix_meets_segment_only_start
      hr hs hrs hvPrefix (by
        simpa [rlc_rightAmbientTraceCanonicalSegment, WR] using hvSegment)
  · rcases rlc_bookOuterTraceNetworkArc_support_cases
        gamma gamma' hs hsLeft hvOuter with hvRight | hvDetour | hvLeft
    · exact (rlc_isPath_takeUntil_dropUntil_contact WR
        (rlc_ambientCrossingWalk_isPath gamma.1) hrW hsW hrs
          hvPrefix (by simpa [WR] using hvRight)).1
    · have hvWR : v ∈ WR.support :=
        WR.support_takeUntil_subset_support hrW (by simpa [WR] using hvPrefix)
      have hvPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 v).1
          hvWR
      have hvEnd :=
        rlc_bookExteriorEndpointDetour_meets_rightTrace_only_endpoint
          hfaith hvDetour hvPath
      have hvIdx : WR.support.idxOf v ≤ WR.support.idxOf r :=
        rlc_idxOf_le_of_mem_takeUntil WR hrW (by simpa [WR] using hvPrefix)
      have hrLt : WR.support.idxOf r < WR.support.length :=
        List.idxOf_lt_length_of_mem hrW
      have hEndIdx : WR.support.idxOf (gamma.1.2.1 : Site 2) = WR.length :=
        rlc_isPath_idxOf_end WR (rlc_ambientCrossingWalk_isPath gamma.1)
      have hrEnd : WR.support.idxOf r ≤
          WR.support.idxOf (gamma.1.2.1 : Site 2) := by
        rw [hEndIdx]
        rw [SimpleGraph.Walk.length_support] at hrLt
        omega
      have hvr : WR.support.idxOf v = WR.support.idxOf r := by
        rw [hvEnd] at hvIdx ⊢
        exact Nat.le_antisymm hvIdx hrEnd
      exact (List.idxOf_inj hvWR).1 hvr
    · have hvWL : v ∈ (rlc_ambientCrossingWalk gamma'.1).support :=
        (rlc_ambientCrossingWalk gamma'.1).support_takeUntil_subset_support
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma'.1 (rlc_flipX s)).2 hsLeft) hvLeft
      have hvLeftPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 v).1
          hvWL
      have hvRightPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 v).1
          (WR.support_takeUntil_subset_support hrW
            (by simpa [WR] using hvPrefix))
      exact False.elim ((Finset.disjoint_left.mp hfaith.exposed_disjoint)
        hvRightPath hvLeftPath)


theorem rlc_bookTraceNetworkBracket_meets_leftSuffix_only_end
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hvBracket : v ∈ (rlc_bookTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support)
    (hvSuffix : v ∈ ((rlc_ambientCrossingWalk gamma'.1).dropUntil
      (rlc_flipX s)
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (rlc_flipX s)).2 hsLeft)).support) :
    v = rlc_flipX s := by
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hsWL : rlc_flipX s ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft
  have hvWL : v ∈ WL.support :=
    WL.support_dropUntil_subset hsWL (by simpa [WL] using hvSuffix)
  have hvLeftPath :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 v).1
      hvWL
  change v ∈ ((rlc_rightAmbientTraceCanonicalSegment
    gamma hr hs hrs).append
      (rlc_bookOuterTraceNetworkArc gamma gamma' hs hsLeft)).support at hvBracket
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvBracket
  rcases hvBracket with hvSegment | hvOuter
  · have hvRightPath :=
      rlc_rightAmbientTraceCanonicalSegment_support_path
        gamma hr hs hrs hvSegment
    exact False.elim ((Finset.disjoint_left.mp hfaith.exposed_disjoint)
      hvRightPath hvLeftPath)
  · rcases rlc_bookOuterTraceNetworkArc_support_cases
        gamma gamma' hs hsLeft hvOuter with hvRight | hvDetour | hvPrefix
    · have hvWR : v ∈ (rlc_ambientCrossingWalk gamma.1).support :=
        (rlc_ambientCrossingWalk gamma.1).support_dropUntil_subset
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma.1 s).2 hs) hvRight
      have hvRightPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 v).1
          hvWR
      exact False.elim ((Finset.disjoint_left.mp hfaith.exposed_disjoint)
        hvRightPath hvLeftPath)
    · have hvStart :=
        rlc_bookExteriorEndpointDetour_meets_leftTrace_only_endpoint
          hfaith hvDetour hvLeftPath
      have hsIdx : WL.support.idxOf (rlc_flipX s) ≤
          WL.support.idxOf v :=
        rlc_isPath_idxOf_le_of_mem_dropUntil WL
          (rlc_ambientCrossingWalk_isPath gamma'.1) hsWL
            (by simpa [WL] using hvSuffix)
      have hStartIdx : WL.support.idxOf (gamma'.1.1 : Site 2) = 0 := by
        exact rlc_walk_idxOf_start WL
      have hEqIdx : WL.support.idxOf v =
          WL.support.idxOf (rlc_flipX s) := by
        rw [hvStart, hStartIdx] at hsIdx ⊢
        omega
      exact (List.idxOf_inj hvWL).1 hEqIdx
    · exact (rlc_isPath_takeUntil_dropUntil_contact WL
        (rlc_ambientCrossingWalk_isPath gamma'.1) hsWL hsWL le_rfl
          (by simpa [WL] using hvPrefix) (by simpa [WL] using hvSuffix)).1


theorem rlc_bookPhysicalTraceNetworkBracket_meets_rightPrefix_only_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hvBracket : v ∈ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support)
    (hvPrefix : v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil r
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma.1 r).2 hr)).map rlc_dualReflectSymmLatticeHom).support) :
    v = rlc_dualReflect.symm r := by
  change v ∈ ((rlc_bookTraceNetworkBracket
    gamma gamma' hr hs hsLeft hrs).map
      rlc_dualReflectSymmLatticeHom).support at hvBracket
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hvBracket hvPrefix
  obtain ⟨w, hwBracket, hwv⟩ := hvBracket
  obtain ⟨q, hqPrefix, hqv⟩ := hvPrefix
  change rlc_dualReflect.symm w = v at hwv
  change rlc_dualReflect.symm q = v at hqv
  have hwq : w = q := rlc_dualReflect.symm.injective (hwv.trans hqv.symm)
  have hwr := rlc_bookTraceNetworkBracket_meets_rightPrefix_only_start
    hfaith hr hs hsLeft hrs hwBracket (by simpa [hwq] using hqPrefix)
  rw [← hwv, hwr]


theorem rlc_bookPhysicalTraceNetworkBracket_axisSource_not_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hrAxis : r ≠ (gamma.1.1 : Site 2)) :
    phb_doubleDualShift (gamma.1.1 : Site 2) ∉
      (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).support := by
  intro hmem
  have hshift : phb_doubleDualShift (gamma.1.1 : Site 2) =
      rlc_dualReflect.symm (gamma.1.1 : Site 2) := by
    calc
      phb_doubleDualShift (gamma.1.1 : Site 2) =
          phb_doubleDualShift (rlc_flipX (gamma.1.1 : Site 2)) :=
        congrArg phb_doubleDualShift
          (rlc_flipX_eq_self_of_zero gamma.1.1.2.2).symm
      _ = rlc_dualReflect.symm (gamma.1.1 : Site 2) :=
        rlc_doubleDualShift_flipX_eq_dualReflect_symm _
  have hprefix : rlc_dualReflect.symm (gamma.1.1 : Site 2) ∈
      (((rlc_ambientCrossingWalk gamma.1).takeUntil r
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma.1 r).2 hr)).map
          rlc_dualReflectSymmLatticeHom).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨gamma.1.1,
      ((rlc_ambientCrossingWalk gamma.1).takeUntil r
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma.1 r).2 hr)).start_mem_support, rfl⟩
  have heq :=
    rlc_bookPhysicalTraceNetworkBracket_meets_rightPrefix_only_start
      hfaith hr hs hsLeft hrs (by simpa [hshift] using hmem) hprefix
  apply hrAxis
  exact rlc_dualReflect.symm.injective heq.symm


theorem rlc_bookPhysicalTraceNetworkBracket_meets_leftSuffix_only_end
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hvBracket : v ∈ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support)
    (hvSuffix : v ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil
      (rlc_flipX s)
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (rlc_flipX s)).2 hsLeft)).map
          rlc_dualReflectSymmLatticeHom).support) :
    v = rlc_dualReflect.symm (rlc_flipX s) := by
  change v ∈ ((rlc_bookTraceNetworkBracket
    gamma gamma' hr hs hsLeft hrs).map
      rlc_dualReflectSymmLatticeHom).support at hvBracket
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hvBracket hvSuffix
  obtain ⟨w, hwBracket, hwv⟩ := hvBracket
  obtain ⟨q, hqSuffix, hqv⟩ := hvSuffix
  change rlc_dualReflect.symm w = v at hwv
  change rlc_dualReflect.symm q = v at hqv
  have hwq : w = q := rlc_dualReflect.symm.injective (hwv.trans hqv.symm)
  have hws := rlc_bookTraceNetworkBracket_meets_leftSuffix_only_end
    hfaith hr hs hsLeft hrs hwBracket (by simpa [hwq] using hqSuffix)
  rw [← hwv, hws]


theorem rlc_bookPhysicalTraceNetworkBracket_meets_sourceTraceCollars_only_ends
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hvBracket : v ∈ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support)
    (hvCollar :
      v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil r
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma.1 r).2 hr)).map rlc_dualReflectSymmLatticeHom).support ∨
      v ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil
        (rlc_flipX s)
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 (rlc_flipX s)).2 hsLeft)).map
            rlc_dualReflectSymmLatticeHom).support) :
    v = rlc_dualReflect.symm r ∨
      v = rlc_dualReflect.symm (rlc_flipX s) := by
  rcases hvCollar with hvRight | hvLeft
  · exact Or.inl
      (rlc_bookPhysicalTraceNetworkBracket_meets_rightPrefix_only_start
        hfaith hr hs hsLeft hrs hvBracket hvRight)
  · exact Or.inr
      (rlc_bookPhysicalTraceNetworkBracket_meets_leftSuffix_only_end
        hfaith hr hs hsLeft hrs hvBracket hvLeft)


theorem rlc_bookPhysicalTraceNetworkBracket_mem_rect
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hv : v ∈ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support) :
    v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1) := by
  change v ∈ ((rlc_bookTraceNetworkBracket
    gamma gamma' hr hs hsLeft hrs).map
      rlc_dualReflectSymmLatticeHom).support at hv
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  change w ∈ ((rlc_rightAmbientTraceCanonicalSegment
    gamma hr hs hrs).append
      (rlc_bookOuterTraceNetworkArc gamma gamma' hs hsLeft)).support at hw
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hwSegment | hwOuter
  · have hwPath := rlc_rightAmbientTraceCanonicalSegment_support_path
      gamma hr hs hrs hwSegment
    have hwBox := rlc_pathVertex_mem_rect gamma.1 hwPath
    change rlc_dualReflect.symm w ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1)
    rw [mem_rect] at hwBox ⊢
    simp only [rlc_dualReflect_symm_zero, rlc_dualReflect_symm_one]
    omega
  · have hwBox : w ∈
        rect (-2 * n - 2) (2 * n + 2) (-n) (n + 2) := by
      rcases rlc_bookOuterTraceNetworkArc_support_cases
          gamma gamma' hs hsLeft hwOuter with hwRight | hwDetour | hwLeft
      · have hwWR := (rlc_ambientCrossingWalk gamma.1).support_dropUntil_subset
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma.1 s).2 hs) hwRight
        have hwPath :=
          (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 w).1
            hwWR
        have h := rlc_pathVertex_mem_rect gamma.1 hwPath
        rw [mem_rect] at h ⊢
        omega
      · exact rlc_bookExteriorEndpointDetour_mem_rect gamma gamma' hwDetour
      · have hwWL :=
          (rlc_ambientCrossingWalk gamma'.1).support_takeUntil_subset_support
            ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
              gamma'.1 (rlc_flipX s)).2 hsLeft) hwLeft
        have hwPath :=
          (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 w).1
            hwWL
        have h := rlc_pathVertex_mem_rect gamma'.1 hwPath
        rw [mem_rect] at h ⊢
        omega
    change rlc_dualReflect.symm w ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1)
    rw [mem_rect] at hwBox ⊢
    simp only [rlc_dualReflect_symm_zero, rlc_dualReflect_symm_one]
    omega


theorem rlc_bookPhysicalTraceNetworkBracket_exteriorPoint_mem
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
    rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈
      (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).support := by
  change rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈
    ((rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).map
      rlc_dualReflectSymmLatticeHom).support
  rw [SimpleGraph.Walk.support_map, List.mem_map]
  refine ⟨![(2 * n + 2), n + 2], ?_, rfl⟩
  change (![(2 * n + 2), n + 2] : Site 2) ∈
    ((rlc_rightAmbientTraceCanonicalSegment gamma hr hs hrs).append
      (rlc_bookOuterTraceNetworkArc gamma gamma' hs hsLeft)).support
  rw [SimpleGraph.Walk.mem_support_append_iff]
  right
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hsWR : s ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs
  have hsWL : rlc_flipX s ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft
  change (![(2 * n + 2), n + 2] : Site 2) ∈
    (((WR.dropUntil s hsWR).append
      (rlc_bookExteriorEndpointDetour gamma gamma')).append
        (WL.takeUntil (rlc_flipX s) hsWL)).support
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl (Or.inr
    (rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'))


theorem rlc_bookTraceNetworkBracket_prefix_exterior_support_cases
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hd : (![(2 * n + 2), n + 2] : Site 2) ∈
      (rlc_bookTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).support)
    (hv : v ∈ ((rlc_bookTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).takeUntil
        (![(2 * n + 2), n + 2] : Site 2) hd).support) :
    v ∈ rlc_pathVertices gamma.1 ∨
      v ∈ (sw_lshape ((gamma.1.2.1 : Site 2) 0)
        ((gamma.1.2.1 : Site 2) 1) (2 * n + 2) (n + 2)).support := by
  let A := rlc_rightAmbientTraceCanonicalSegment gamma hr hs hrs
  let WR := rlc_ambientCrossingWalk gamma.1
  let R := WR.dropUntil s
    ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs)
  let D := rlc_bookExteriorEndpointDetour gamma gamma'
  let WL := rlc_ambientCrossingWalk gamma'.1
  let L := WL.takeUntil (rlc_flipX s)
    ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft)
  let rightLeg : (hypercubicLattice 2).Walk
      (gamma.1.2.1 : Site 2) ![2 * n + 2, n + 2] := by
    let rr : Site 2 := gamma.1.2.1
    have hrr : (![rr 0, rr 1] : Site 2) = rr := by
      ext i
      fin_cases i <;> simp
    exact (sw_lshape (rr 0) (rr 1) (2 * n + 2) (n + 2)).copy hrr rfl
  let topLeg := sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2)
  let leftLeg : (hypercubicLattice 2).Walk
      ![-2 * n - 2, n + 2] (gamma'.1.1 : Site 2) := by
    let ll : Site 2 := gamma'.1.1
    have hll : (![ll 0, ll 1] : Site 2) = ll := by
      ext i
      fin_cases i <;> simp
    exact ((sw_lshape (ll 0) (ll 1) (-2 * n - 2) (n + 2)).reverse).copy
      rfl hll
  let d : Site 2 := ![2 * n + 2, n + 2]
  have hdRight : d ∈ rightLeg.support := rightLeg.end_mem_support
  have hdA : d ∉ A.support := by
    intro h
    have hp := rlc_rightAmbientTraceCanonicalSegment_support_path
      gamma hr hs hrs h
    have hb := rlc_pathVertex_mem_rect gamma.1 hp
    rw [mem_rect] at hb
    simp [d] at hb
  have hdR : d ∉ R.support := by
    intro h
    have hWR := WR.support_dropUntil_subset
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs) h
    have hp := (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 d).1 hWR
    have hb := rlc_pathVertex_mem_rect gamma.1 hp
    rw [mem_rect] at hb
    simp [d] at hb
  have hdD : d ∈ D.support := by
    exact rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'
  have hD : D = (rightLeg.append topLeg).append leftLeg := by
    simp only [D, rlc_bookExteriorEndpointDetour, rightLeg, topLeg, leftLeg]
  have hW : rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs =
      A.append ((R.append D).append L) := by
    rfl
  have htakeD : D.takeUntil d hdD = rightLeg.takeUntil d hdRight := by
    have hdRT : d ∈ (rightLeg.append topLeg).support :=
      SimpleGraph.Walk.subset_support_append_left rightLeg topLeg hdRight
    simp only [hD]
    calc
      ((rightLeg.append topLeg).append leftLeg).takeUntil d _ =
          (rightLeg.append topLeg).takeUntil d hdRT :=
        SimpleGraph.Walk.takeUntil_append_of_mem_left _ _ _
      _ = rightLeg.takeUntil d hdRight :=
        SimpleGraph.Walk.takeUntil_append_of_mem_left _ _ _
  have hdRD : d ∈ (R.append D).support :=
    SimpleGraph.Walk.subset_support_append_right R D hdD
  have htakeRD : (R.append D).takeUntil d hdRD =
      R.append (rightLeg.takeUntil d hdRight) := by
    rw [rlc_walk_takeUntil_append_of_notMem_left R D hdR hdD]
    rw [htakeD]
  have hdOuter : d ∈ ((R.append D).append L).support :=
    SimpleGraph.Walk.subset_support_append_left (R.append D) L hdRD
  have htakeOuter : ((R.append D).append L).takeUntil d hdOuter =
      R.append (rightLeg.takeUntil d hdRight) := by
    rw [SimpleGraph.Walk.takeUntil_append_of_mem_left]
    exact htakeRD
  have htakeW :
      (rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).takeUntil d hd =
        A.append (R.append (rightLeg.takeUntil d hdRight)) := by
    simp only [hW]
    rw [rlc_walk_takeUntil_append_of_notMem_left A _ hdA hdOuter]
    rw [htakeOuter]
  rw [htakeW, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hvA | hvR | hvLeg
  · exact Or.inl (rlc_rightAmbientTraceCanonicalSegment_support_path
      gamma hr hs hrs hvA)
  · left
    exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 v).1
      (WR.support_dropUntil_subset
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs)
        hvR)
  · right
    change v ∈ (sw_lshape _ _ _ _).support
    have hvRight := SimpleGraph.Walk.support_takeUntil_subset_support
      rightLeg hdRight hvLeg
    simpa only [rightLeg, SimpleGraph.Walk.support_copy] using hvRight


theorem rlc_bookPhysicalTraceNetworkBracket_beforeExterior_boundaryContact_right
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    {k : Nat}
    (hk : k < (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support.idxOf
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)))
    (hkBoundary : (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).getVert k ∈ (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).getVert k) ∈
        rlc_pathVertices gamma.1 := by
  let W := rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs
  let B := rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs
  let d : Site 2 := ![2 * n + 2, n + 2]
  have hB : B = W.map rlc_dualReflectSymmLatticeHom := rfl
  have hdW : d ∈ W.support := by
    change d ∈ ((rlc_rightAmbientTraceCanonicalSegment
      gamma hr hs hrs).append
        (rlc_bookOuterTraceNetworkArc gamma gamma' hs hsLeft)).support
    rw [SimpleGraph.Walk.mem_support_append_iff]
    right
    let WR := rlc_ambientCrossingWalk gamma.1
    let WL := rlc_ambientCrossingWalk gamma'.1
    have hsWR : s ∈ WR.support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs
    have hsWL : rlc_flipX s ∈ WL.support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (rlc_flipX s)).2 hsLeft
    change d ∈ (((WR.dropUntil s hsWR).append
      (rlc_bookExteriorEndpointDetour gamma gamma')).append
        (WL.takeUntil (rlc_flipX s) hsWL)).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inr
      (rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'))
  have hidx : B.support.idxOf (rlc_dualReflect.symm d) =
      W.support.idxOf d := by
    rw [hB]
    have hsupportMap :
        (W.map rlc_dualReflectSymmLatticeHom).support =
          W.support.map rlc_dualReflect.symm :=
      SimpleGraph.Walk.support_map rlc_dualReflectSymmLatticeHom W
    calc
      (W.map rlc_dualReflectSymmLatticeHom).support.idxOf
          (rlc_dualReflect.symm d) =
          (W.support.map rlc_dualReflect.symm).idxOf
            (rlc_dualReflect.symm d) :=
        congrArg (fun l => l.idxOf (rlc_dualReflect.symm d)) hsupportMap
      _ = W.support.idxOf d := rlc_list_idxOf_map_of_injective _
        rlc_dualReflect.symm.injective _ _
  have hkTake : k ≤ (W.takeUntil d hdW).length := by
    rw [SimpleGraph.Walk.length_takeUntil, ← hidx]
    simpa only [B, d] using hk.le
  have hget : (W.takeUntil d hdW).getVert k = W.getVert k :=
    W.getVert_takeUntil hdW hkTake
  have hwPrefix : W.getVert k ∈ (W.takeUntil d hdW).support := by
    rw [← hget]
    exact (W.takeUntil d hdW).getVert_mem_support k
  rcases rlc_bookTraceNetworkBracket_prefix_exterior_support_cases
      gamma gamma' hr hs hsLeft hrs hdW hwPrefix with hwRight | hwLeg
  · change rlc_dualReflect (B.getVert k) ∈ rlc_pathVertices gamma.1
    rw [hB]
    have hgetMap : (W.map rlc_dualReflectSymmLatticeHom).getVert k =
        rlc_dualReflect.symm (W.getVert k) :=
      SimpleGraph.Walk.getVert_map rlc_dualReflectSymmLatticeHom W k
    have heq : rlc_dualReflect
        ((W.map rlc_dualReflectSymmLatticeHom).getVert k) = W.getVert k := by
      calc
        _ = rlc_dualReflect (rlc_dualReflect.symm (W.getVert k)) :=
          congrArg rlc_dualReflect hgetMap
        _ = _ := rlc_dualReflect.apply_symm_apply _
    exact heq.symm ▸ hwRight
  · have hsourceBoundary : rlc_dualReflect.symm (W.getVert k) ∈
        (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support := by
      change B.getVert k ∈ (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support at hkBoundary
      rw [hB] at hkBoundary
      have hgetMap : (W.map rlc_dualReflectSymmLatticeHom).getVert k =
          rlc_dualReflect.symm (W.getVert k) :=
        SimpleGraph.Walk.getVert_map rlc_dualReflectSymmLatticeHom W k
      exact hgetMap ▸ hkBoundary
    have hwEq :=
      rlc_bookPhysicalRightEndpointLeg_meets_filledBoundary_only_endpoint
        hn gamma gamma' omega hwLeg hsourceBoundary
    change rlc_dualReflect (B.getVert k) ∈ rlc_pathVertices gamma.1
    rw [hB]
    have hgetMap : (W.map rlc_dualReflectSymmLatticeHom).getVert k =
        rlc_dualReflect.symm (W.getVert k) :=
      SimpleGraph.Walk.getVert_map rlc_dualReflectSymmLatticeHom W k
    have heq : rlc_dualReflect
        ((W.map rlc_dualReflectSymmLatticeHom).getVert k) = W.getVert k := by
      calc
        _ = rlc_dualReflect (rlc_dualReflect.symm (W.getVert k)) :=
          congrArg rlc_dualReflect hgetMap
        _ = _ := rlc_dualReflect.apply_symm_apply _
    have hend := (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (gamma.1.2.1 : Site 2)).1
        (rlc_ambientCrossingWalk gamma.1).end_mem_support
    exact heq.symm ▸ hwEq.symm ▸ hend


theorem rlc_bookPhysicalTraceNetworkBracket_contactExtrema
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {r s u : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hstart : rlc_dualReflect.symm r ∈ c.support)
    (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support) :
    let B := rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs
    let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
    let k := B.support.idxOf d
    ∃ i j : Nat,
      i < k ∧ k < j ∧ j ≤ B.length ∧
        B.getVert i ∈ c.support ∧ B.getVert j ∈ c.support ∧
        B.getVert k = d ∧
        (∀ l : Nat, i < l → l < j → B.getVert l ∉ c.support) ∧
        (∀ l : Nat, i < l → l < j →
          B.getVert l ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∧
        rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧
        (rlc_dualReflect (B.getVert j) ∈ rlc_pathVertices gamma.1 ∨
          rlc_dualReflect (B.getVert j) ∈ rlc_pathVertices gamma'.1 ∨
          B.getVert j = rlc_dualReflect.symm
            (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) := by
  dsimp only
  let B := rlc_bookPhysicalTraceNetworkBracket
    gamma gamma' hr hs hsLeft hrs
  let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
  have hdB : d ∈ B.support := by
    exact rlc_bookPhysicalTraceNetworkBracket_exteriorPoint_mem
      gamma gamma' hr hs hsLeft hrs
  have hdOff : d ∉ c.support := by
    intro hdc
    have hdBox := rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox
      hn gamma gamma' omega c hcycle hdc
    rw [mem_rect] at hdBox
    dsimp only [d] at hdBox
    simp only [rlc_dualReflect_symm_zero, Matrix.cons_val_zero] at hdBox
    omega
  let k := B.support.idxOf d
  have hkLength : k ≤ B.length := by
    have hk := List.idxOf_lt_length_of_mem hdB
    rw [SimpleGraph.Walk.length_support] at hk
    omega
  have hkGet : B.getVert k = d := by
    exact B.getVert_support_idxOf hdB
  obtain ⟨i, j, hik, hkj, hjLength, hi, hj, hbetween⟩ :=
    rlc_walk_exists_contact_extrema_around_offSupport
      B (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))
      hkLength (by
        simpa [B, SimpleGraph.Walk.support_mapLe_eq_support] using hstart)
      (by simpa [B, SimpleGraph.Walk.support_mapLe_eq_support] using hend)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support, hkGet] using hdOff)
  have hregion :=
    rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle
  have hdOutside : d ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rw [← hregion]
    intro hdFilled
    have hdBox := rlc_twoChannelFullFilledReachSet_subset_connectorRect
      hn gamma gamma' omega hdFilled
    rw [mem_rect] at hdBox
    dsimp only [d] at hdBox
    simp only [rlc_dualReflect_symm_zero, Matrix.cons_val_zero] at hdBox
    omega
  have hside := rlc_walk_contactInterval_same_leftRegion_side
    B (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))
    hik hkj hjLength (by
      intro l hil hlj
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using
        hbetween l hil hlj) (by simpa [hkGet] using hdOutside)
  have hcNotNil : ¬c.Nil := by
    intro hnil
    exact hcycle.ne_nil hnil.eq_nil
  have cycleSupport {v : Site 2} (hv : v ∈ c.support) :
      v ∈ (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support := by
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
  have hiProv :=
    rlc_bookPhysicalTraceNetworkBracket_beforeExterior_boundaryContact_right
      hn gamma gamma' omega hr hs hsLeft hrs (by
        simpa [B, d, k] using hik) (cycleSupport (by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hi))
  have hjProv :=
    rlc_bookPhysicalTraceNetworkBracket_boundaryContact_provenance
      hn gamma gamma' omega hr hs hsLeft hrs
        (B.getVert_mem_support j) (cycleSupport (by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hj))
  refine ⟨i, j, hik, hkj, hjLength, ?_, ?_, hkGet, ?_, hside,
    hiProv, hjProv⟩
  · simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hi
  · simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hj
  · intro l hil hlj
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hbetween l hil hlj


theorem rlc_bookPhysicalTraceNetworkBracket_ordered_contactExtrema
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {r s u : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hstart : rlc_dualReflect.symm r ∈ c.support)
    (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support) :
    let B := rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs
    let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
    let k := B.support.idxOf d
    ∃ i j : Nat,
      i < k ∧ k < j ∧ j ≤ B.length ∧
        B.getVert i ∈ c.support ∧ B.getVert j ∈ c.support ∧
        B.getVert k = d ∧
        (∀ l : Nat, i < l → l < j → B.getVert l ∉ c.support) ∧
        (∀ l : Nat, i < l → l < j →
          B.getVert l ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∧
        rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧
        (rlc_dualReflect (B.getVert j) ∈ rlc_pathVertices gamma'.1 ∨
          B.getVert j = rlc_dualReflect.symm
            (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) := by
  dsimp only
  obtain ⟨i, j, hik, hkj, hjLength, hi, hj, hkGet, hbetween,
      hside, hiRight, hjProv⟩ :=
    rlc_bookPhysicalTraceNetworkBracket_contactExtrema
      hn gamma gamma' omega hr hs hsLeft hrs c hcycle hstart hend
  have hjGood :
      rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert j) ∈
          rlc_pathVertices gamma'.1 ∨
        (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j =
            rlc_dualReflect.symm
              (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
    rcases hjProv with hjRight | hjLeft | hjCollar
    · have hjLe :=
        rlc_bookPhysicalTraceNetworkBracket_right_index_le_exterior
          hn hfaith hr hs hsLeft hrs hjLength hjRight
      omega
    · exact Or.inl hjLeft
    · exact Or.inr hjCollar
  exact ⟨i, j, hik, hkj, hjLength, hi, hj, hkGet, hbetween,
    hside, hiRight, hjGood⟩


theorem rlc_bookPhysicalTraceNetworkBracket_next_left_after_collar
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {r s u : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support)
    {j : Nat}
    (hjLength : j ≤ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).length)
    (hkltj : (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support.idxOf
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) < j)
    (hjCollar : (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).getVert j =
        rlc_dualReflect.symm
          (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) :
    ∃ j' : Nat,
      j < j' ∧
        j' ≤ (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).length ∧
        (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j' ∈ c.support ∧
        rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j') ∈
            rlc_pathVertices gamma'.1 ∧
        ∀ l : Nat, j < l → l < j' →
          (rlc_bookPhysicalTraceNetworkBracket
            gamma gamma' hr hs hsLeft hrs).getVert l ∉ c.support := by
  let B := rlc_bookPhysicalTraceNetworkBracket
    gamma gamma' hr hs hsLeft hrs
  let w : Site 2 :=
    ![-2 * n - 1, (gamma'.1.1 : Site 2) 1]
  let collar : Site 2 := rlc_dualReflect.symm w
  have hEndNe : rlc_dualReflect.symm (rlc_flipX s) ≠ collar := by
    intro hEq
    have hEq' : rlc_dualReflect.symm (rlc_flipX s) =
        rlc_dualReflect.symm w := by
      simpa only [B, collar] using hEq
    have hsource : rlc_flipX s = w :=
      rlc_dualReflect.symm.injective hEq'
    have h0 := congrArg (fun z : Site 2 => z 0) hsource
    have hsBox := rlc_pathVertex_mem_rect gamma.1 hs
    rw [mem_rect] at hsBox
    change -(s 0) = -2 * n - 1 at h0
    omega
  have hjStrict : j < B.length := by
    have hjLength' : j ≤ B.length := by simpa [B] using hjLength
    apply lt_of_le_of_ne hjLength'
    intro hjEq
    apply hEndNe
    calc
      rlc_dualReflect.symm (rlc_flipX s) = B.getVert B.length :=
        B.getVert_length.symm
      _ = B.getVert j := by rw [hjEq]
      _ = collar := by simpa [B, collar, w] using hjCollar
  let C := c.mapLe (faceBoundaryGraph_le
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
  obtain ⟨j', hjj', hj'Length, hj'Contact, hbetween⟩ :=
    rlc_walk_exists_first_contact_after B C hjStrict (by
      simpa [B, C, SimpleGraph.Walk.support_mapLe_eq_support] using hend)
  have hj'ContactC : B.getVert j' ∈ c.support := by
    simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hj'Contact
  have hcNotNil : ¬c.Nil := by
    intro hnil
    exact hcycle.ne_nil hnil.eq_nil
  have cycleSupport {v : Site 2} (hv : v ∈ c.support) :
      v ∈ (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support := by
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
  have hj'Prov :=
    rlc_bookPhysicalTraceNetworkBracket_boundaryContact_provenance
      hn gamma gamma' omega hr hs hsLeft hrs
        (B.getVert_mem_support j') (cycleSupport hj'ContactC)
  have hj'Left : rlc_dualReflect (B.getVert j') ∈
      rlc_pathVertices gamma'.1 := by
    rcases hj'Prov with hj'Right | hj'Left | hj'Collar
    · have hj'Le :=
        rlc_bookPhysicalTraceNetworkBracket_right_index_le_exterior
          hn hfaith hr hs hsLeft hrs hj'Length hj'Right
      omega
    · exact hj'Left
    · have hBPath := rlc_bookPhysicalTraceNetworkBracket_isPath
        hn hfaith hr hs hsLeft hrs
      have hjEq : B.getVert j' = B.getVert j := by
        calc
          B.getVert j' = collar := by
            simpa [B, collar, w] using hj'Collar
          _ = B.getVert j := by
            simpa [B, collar, w] using hjCollar.symm
      have : j' = j := hBPath.getVert_injOn hj'Length
        (by simpa [B] using hjLength) hjEq
      omega
  refine ⟨j', hjj', hj'Length, hj'ContactC, hj'Left, ?_⟩
  intro l hjl hlj
  simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using
    hbetween l hjl hlj


theorem rlc_path_edges_disjoint_of_endpoint_intersection
    {V : Type*} {G : SimpleGraph V} {u v d : V}
    {p : G.Walk u v} {q : G.Walk v u}
    (hp : p.IsPath) (hd : d ∈ p.support) (hdu : d ≠ u) (hdv : d ≠ v)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v) :
    p.edges.Disjoint q.edges := by
  rw [List.disjoint_left]
  intro e hep heq
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hx := hinter x
        (p.fst_mem_support_of_mem_edges hep)
        (q.fst_mem_support_of_mem_edges heq)
      have hy := hinter y
        (p.snd_mem_support_of_mem_edges hep)
        (q.snd_mem_support_of_mem_edges heq)
      have hxy := p.adj_of_mem_edges hep
      have heqUV : s(x, y) = s(u, v) := by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact False.elim (hxy.ne rfl)
        · rfl
        · exact Sym2.eq_swap
        · exact False.elim (hxy.ne rfl)
      have huvEdge : s(u, v) ∈ p.edges := by
        rw [← heqUV]
        exact hep
      have huv := p.adj_of_mem_edges huvEdge
      rcases (p.isSubwalk_toWalk_iff_mem_edges huv).2 huvEdge with
          hforward | hreverse
      · obtain ⟨ru, rv, hpEq⟩ := hforward
        have hwhole : ((ru.append huv.toWalk).append rv).IsPath := by
          rw [← hpEq]
          exact hp
        have hruNil : ru = .nil :=
          ru.isPath_iff_eq_nil.mp hwhole.of_append_left.of_append_left
        have hrvNil : rv = .nil :=
          rv.isPath_iff_eq_nil.mp hwhole.of_append_right
        have hpDirect : p = huv.toWalk := by
          rw [hpEq, hruNil, hrvNil]
          simp
        rw [hpDirect] at hd
        simp [SimpleGraph.Adj.toWalk] at hd
        exact hd.elim hdu hdv
      · obtain ⟨ru, rv, hpEq⟩ := hreverse
        have hwhole : ((ru.append huv.symm.toWalk).append rv).IsPath := by
          rw [← hpEq]
          exact hp
        have hprefixNil : ru.append huv.symm.toWalk = .nil :=
          (ru.append huv.symm.toWalk).isPath_iff_eq_nil.mp
            hwhole.of_append_left
        have hlength := congrArg SimpleGraph.Walk.length hprefixNil
        simp at hlength


theorem rlc_exteriorChord_complementaryArcCycles
    {H K : SimpleGraph (Site 2)} (hHK : H ≤ K)
    {u a b d : Site 2}
    (c : H.Walk u u) (hc : c.IsCycle)
    (p : K.Walk a b) (hp : p.IsPath)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hdp : d ∈ p.support) (hdc : d ∉ c.support)
    (hclean : ∀ x ∈ p.support, x = a ∨ x = b ∨ x ∉ c.support) :
    (p.append ((rlc_orderedContourArc c ha hb).mapLe hHK).reverse).IsCycle ∧
      (p.append
        ((rlc_complementaryContourArc c ha hb).mapLe hHK).reverse).IsCycle := by
  have hda : d ≠ a := by
    intro h
    exact hdc (h ▸ ha)
  have hdb : d ≠ b := by
    intro h
    exact hdc (h ▸ hb)
  have hab : a ≠ b := by
    intro h
    subst b
    have hpNil : p = .nil := p.isPath_iff_eq_nil.mp hp
    have hda' : d = a := by
      simpa [hpNil] using hdp
    exact hda hda'
  have horderedPath :
      ((rlc_orderedContourArc c ha hb).mapLe hHK).IsPath :=
    (SimpleGraph.Walk.mapLe_isPath hHK).2
      (rlc_orderedContourArc_isPath c hc ha hb)
  have hcomplementaryPath :
      ((rlc_complementaryContourArc c ha hb).mapLe hHK).IsPath :=
    (SimpleGraph.Walk.mapLe_isPath hHK).2
      (rlc_complementaryContourArc_isPath c hc ha hb hab)
  have hinterOrdered : ∀ x, x ∈ p.support →
      x ∈ ((rlc_orderedContourArc c ha hb).mapLe hHK).reverse.support →
      x = a ∨ x = b := by
    intro x hxp hxq
    have hxc : x ∈ c.support :=
      rlc_orderedContourArc_support_subset c ha hb (by
        simpa [SimpleGraph.Walk.support_reverse,
          SimpleGraph.Walk.support_mapLe_eq_support] using hxq)
    rcases hclean x hxp with hxa | hxb | hnot
    · exact Or.inl hxa
    · exact Or.inr hxb
    · exact False.elim (hnot hxc)
  have hinterComplementary : ∀ x, x ∈ p.support →
      x ∈ ((rlc_complementaryContourArc c ha hb).mapLe hHK).reverse.support →
      x = a ∨ x = b := by
    intro x hxp hxq
    have hxc : x ∈ c.support :=
      rlc_complementaryContourArc_support_subset c ha hb (by
        simpa [SimpleGraph.Walk.support_reverse,
          SimpleGraph.Walk.support_mapLe_eq_support] using hxq)
    rcases hclean x hxp with hxa | hxb | hnot
    · exact Or.inl hxa
    · exact Or.inr hxb
    · exact False.elim (hnot hxc)
  constructor
  · exact rlc_append_isCycle_of_endpoint_intersection hp
      horderedPath.reverse hab hinterOrdered
      (rlc_path_edges_disjoint_of_endpoint_intersection hp hdp hda hdb
        hinterOrdered)
  · exact rlc_append_isCycle_of_endpoint_intersection hp
      hcomplementaryPath.reverse hab hinterComplementary
      (rlc_path_edges_disjoint_of_endpoint_intersection hp hdp hda hdb
        hinterComplementary)


theorem rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff
    {a f g p q : Site 2}
    (C : (hypercubicLattice 2).Walk a a)
    (hnd : C.edges.Nodup)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hshared : sharedPrimalEdge f g = s(p, q)) :
    rlc_OppositeLoopSides C p q ↔ s(f, g) ∈ C.edges := by
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor]
  have hflip := StatMech.Walls.rpc_crossFlip C hpq
  rw [bdEdge_mk, rlc_crossEdge_eq_flankFaces hpq,
    rlc_flankFaces_eq_of_sharedPrimalEdge_eq hfg hshared,
    StatMech.Walls.dow_odd_count_iff_mem_of_nodup hnd] at hflip
  tauto


theorem rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff_oddCount
    {a f g p q : Site 2}
    (C : (hypercubicLattice 2).Walk a a)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hshared : sharedPrimalEdge f g = s(p, q)) :
    rlc_OppositeLoopSides C p q ↔ Odd (C.edges.count s(f, g)) := by
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor]
  have hflip := StatMech.Walls.rpc_crossFlip C hpq
  rw [bdEdge_mk, rlc_crossEdge_eq_flankFaces hpq,
    rlc_flankFaces_eq_of_sharedPrimalEdge_eq hfg hshared] at hflip
  tauto


theorem rlc_two_terminalFlanks_oppositeLoopSides_of_countParity
    {a f g f' g' p q p' q' : Site 2}
    (C : (hypercubicLattice 2).Walk a a)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfg' : (hypercubicLattice 2).Adj f' g')
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hshared' : sharedPrimalEdge f' g' = s(p', q'))
    (Q : (hypercubicLattice 2).Walk q q')
    (hQoff : ∀ z ∈ Q.support, z ∉ C.support)
    (hRodd : Odd (C.edges.count s(f, g)))
    (hLeven : Even (C.edges.count s(f', g'))) :
    rlc_OppositeLoopSides C p p' := by
  have hR := (rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff_oddCount
    C hfg hpq hshared).2 hRodd
  have hLnot : ¬ rlc_OppositeLoopSides C p' q' := by
    rw [rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff_oddCount
      C hfg' hpq' hshared']
    exact Nat.not_odd_iff_even.mpr hLeven
  have hsame := jlri_sameRegion_along_offSupport_walk C Q hQoff
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor] at hR hLnot ⊢
  tauto


theorem rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_orderedArc
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u x y f g f' g' p q p' q' : Site 2}
    (c : G.Walk u u) (hc : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (B : (hypercubicLattice 2).Walk x y)
    (hR : s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges)
    (hL : s(f', g') ∈ (rlc_complementaryContourArc c hx hy).edges)
    (hfB : f ∉ B.support) (hf'B : f' ∉ B.support)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfg' : (hypercubicLattice 2).Adj f' g')
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hshared' : sharedPrimalEdge f' g' = s(p', q'))
    (Q : (hypercubicLattice 2).Walk q q')
    (W : (hypercubicLattice 2).Walk p p')
    (hQW : Q.support ⊆ W.support) :
    (∃ z ∈ W.support, z ∈ B.support) ∨
      ∃ z ∈ W.support, z ∈ (rlc_orderedContourArc c hx hy).support := by
  classical
  let A := rlc_orderedContourArc c hx hy
  let C := B.append (A.mapLe hG).reverse
  by_cases hArc : ∃ z ∈ W.support, z ∈ A.support
  · right
    simpa [A] using hArc
  left
  by_contra hB
  have hWoffB : ∀ z ∈ W.support, z ∉ B.support := by
    intro z hzW hzB
    exact hB ⟨z, hzW, hzB⟩
  have hWoffA : ∀ z ∈ W.support, z ∉ A.support := by
    intro z hzW hzA
    exact hArc ⟨z, hzW, hzA⟩
  have hQoff : ∀ z ∈ Q.support, z ∉ C.support := by
    intro z hzQ hzC
    have hzW := hQW hzQ
    simp only [C, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.support_mapLe_eq_support, List.mem_reverse] at hzC
    exact hzC.elim (hWoffB z hzW) (hWoffA z hzW)
  have hRB : s(f, g) ∉ B.edges := by
    intro he
    exact hfB (B.fst_mem_support_of_mem_edges he)
  have hLB : s(f', g') ∉ B.edges := by
    intro he
    exact hf'B (B.fst_mem_support_of_mem_edges he)
  have hdis := rlc_orderedContourArc_edges_disjoint_complementary
    c hc.isTrail hx hy
  have hLnotA : s(f', g') ∉ A.edges := by
    intro he
    exact hdis he hL
  have hAtrail : A.IsTrail :=
    (rlc_orderedContourArc_isPath c hc hx hy).isTrail
  have hRoddA : Odd (A.edges.count s(f, g)) :=
    (StatMech.Walls.dow_odd_count_iff_mem_of_nodup
      hAtrail.edges_nodup s(f, g)).2 hR
  have hRoddC : Odd (C.edges.count s(f, g)) := by
    simpa only [C, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse,
      SimpleGraph.Walk.edges_mapLe_eq_edges, List.count_append,
      List.count_reverse, (List.count_eq_zero.mpr hRB), Nat.zero_add] using
        hRoddA
  have hLevenC : Even (C.edges.count s(f', g')) := by
    simp only [C, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse,
      SimpleGraph.Walk.edges_mapLe_eq_edges, List.count_append,
      List.count_reverse, (List.count_eq_zero.mpr hLB),
      (List.count_eq_zero.mpr hLnotA), Nat.zero_add]
    exact ⟨0, by omega⟩
  have hopp := rlc_two_terminalFlanks_oppositeLoopSides_of_countParity
    C hfg hfg' hpq hpq' hshared hshared' Q hQoff hRoddC hLevenC
  obtain ⟨z, hzW, hzC⟩ := rlc_closedLoop_contact_of_opposite_sides C W hopp
  simp only [C, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse,
    SimpleGraph.Walk.support_mapLe_eq_support, List.mem_reverse] at hzC
  exact hzC.elim (hWoffB z hzW) (hWoffA z hzW)


theorem rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_complementaryArc
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u x y f g f' g' p q p' q' : Site 2}
    (c : G.Walk u u) (hc : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (B : (hypercubicLattice 2).Walk x y)
    (hR : s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges)
    (hL : s(f', g') ∈ (rlc_complementaryContourArc c hx hy).edges)
    (hfB : f ∉ B.support) (hf'B : f' ∉ B.support)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfg' : (hypercubicLattice 2).Adj f' g')
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hshared' : sharedPrimalEdge f' g' = s(p', q'))
    (Q : (hypercubicLattice 2).Walk q q')
    (W : (hypercubicLattice 2).Walk p p')
    (hQW : Q.support ⊆ W.support) :
    (∃ z ∈ W.support, z ∈ B.support) ∨
      ∃ z ∈ W.support,
        z ∈ (rlc_complementaryContourArc c hx hy).support := by
  classical
  let A := rlc_complementaryContourArc c hx hy
  let C := B.append (A.mapLe hG).reverse
  by_cases hArc : ∃ z ∈ W.support, z ∈ A.support
  · right
    simpa [A] using hArc
  left
  by_contra hB
  have hWoffB : ∀ z ∈ W.support, z ∉ B.support := by
    intro z hzW hzB
    exact hB ⟨z, hzW, hzB⟩
  have hWoffA : ∀ z ∈ W.support, z ∉ A.support := by
    intro z hzW hzA
    exact hArc ⟨z, hzW, hzA⟩
  have hQoff : ∀ z ∈ Q.reverse.support, z ∉ C.support := by
    intro z hzQ hzC
    have hzW : z ∈ W.support := hQW (by
      simpa [SimpleGraph.Walk.support_reverse] using hzQ)
    simp only [C, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.support_mapLe_eq_support, List.mem_reverse] at hzC
    exact hzC.elim (hWoffB z hzW) (hWoffA z hzW)
  have hRB : s(f, g) ∉ B.edges := by
    intro he
    exact hfB (B.fst_mem_support_of_mem_edges he)
  have hLB : s(f', g') ∉ B.edges := by
    intro he
    exact hf'B (B.fst_mem_support_of_mem_edges he)
  have hdis := rlc_orderedContourArc_edges_disjoint_complementary
    c hc.isTrail hx hy
  have hRnotA : s(f, g) ∉ A.edges := by
    intro he
    exact hdis hR he
  have hxy : x ≠ y := by
    intro hxy
    have hnil : (rlc_orderedContourArc c hx hy).Nil := by
      unfold rlc_orderedContourArc
      rw [SimpleGraph.Walk.nil_takeUntil]
      exact hxy
    simpa [SimpleGraph.Walk.edges_eq_nil.mpr hnil] using hR
  have hAtrail : A.IsTrail :=
    (rlc_complementaryContourArc_isPath c hc hx hy hxy).isTrail
  have hLoddA : Odd (A.edges.count s(f', g')) :=
    (StatMech.Walls.dow_odd_count_iff_mem_of_nodup
      hAtrail.edges_nodup s(f', g')).2 hL
  have hLoddC : Odd (C.edges.count s(f', g')) := by
    simpa only [C, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse,
      SimpleGraph.Walk.edges_mapLe_eq_edges, List.count_append,
      List.count_reverse, (List.count_eq_zero.mpr hLB), Nat.zero_add] using
        hLoddA
  have hRevenC : Even (C.edges.count s(f, g)) := by
    simp only [C, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse,
      SimpleGraph.Walk.edges_mapLe_eq_edges, List.count_append,
      List.count_reverse, (List.count_eq_zero.mpr hRB),
      (List.count_eq_zero.mpr hRnotA), Nat.zero_add]
    exact ⟨0, by omega⟩
  have hopp := rlc_two_terminalFlanks_oppositeLoopSides_of_countParity
    C hfg' hfg hpq' hpq hshared' hshared Q.reverse hQoff hLoddC hRevenC
  obtain ⟨z, hzW, hzC⟩ :=
    rlc_closedLoop_contact_of_opposite_sides C W.reverse hopp
  have hzW' : z ∈ W.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzW
  simp only [C, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse,
    SimpleGraph.Walk.support_mapLe_eq_support, List.mem_reverse] at hzC
  exact hzC.elim (hWoffB z hzW') (hWoffA z hzW')


theorem rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_bothArcs
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u x y f g f' g' p q p' q' : Site 2}
    (c : G.Walk u u) (hc : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (B : (hypercubicLattice 2).Walk x y)
    (hR : s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges)
    (hL : s(f', g') ∈ (rlc_complementaryContourArc c hx hy).edges)
    (hfB : f ∉ B.support) (hf'B : f' ∉ B.support)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfg' : (hypercubicLattice 2).Adj f' g')
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hshared' : sharedPrimalEdge f' g' = s(p', q'))
    (Q : (hypercubicLattice 2).Walk q q')
    (W : (hypercubicLattice 2).Walk p p')
    (hQW : Q.support ⊆ W.support) :
    (∃ z ∈ W.support, z ∈ B.support) ∨
      ((∃ z ∈ W.support,
          z ∈ (rlc_orderedContourArc c hx hy).support) ∧
        ∃ z ∈ W.support,
          z ∈ (rlc_complementaryContourArc c hx hy).support) := by
  have hordered :=
    rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_orderedArc
      hG c hc hx hy B hR hL hfB hf'B hfg hfg' hpq hpq'
        hshared hshared' Q W hQW
  have hcomplementary :=
    rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_complementaryArc
      hG c hc hx hy B hR hL hfB hf'B hfg hfg' hpq hpq'
        hshared hshared' Q W hQW
  rcases hordered with hB | hordered
  · exact Or.inl hB
  rcases hcomplementary with hB | hcomplementary
  · exact Or.inl hB
  · exact Or.inr ⟨hordered, hcomplementary⟩


theorem rlc_two_terminalFlanks_oppositeLoopSides_of_edgeXor
    {a f g f' g' p q p' q' : Site 2}
    (C : (hypercubicLattice 2).Walk a a)
    (hnd : C.edges.Nodup)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfg' : (hypercubicLattice 2).Adj f' g')
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hshared' : sharedPrimalEdge f' g' = s(p', q'))
    (Q : (hypercubicLattice 2).Walk q q')
    (hQoff : ∀ z ∈ Q.support, z ∉ C.support)
    (hedges : (s(f, g) ∈ C.edges ∧ s(f', g') ∉ C.edges) ∨
      (s(f, g) ∉ C.edges ∧ s(f', g') ∈ C.edges)) :
    rlc_OppositeLoopSides C p p' := by
  have hR := rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff
    C hnd hfg hpq hshared
  have hL := rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff
    C hnd hfg' hpq' hshared'
  have hsame := jlri_sameRegion_along_offSupport_walk C Q hQoff
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor] at hR hL ⊢
  tauto


theorem rlc_cleanChord_contourEdge_not_mem
    {G : SimpleGraph (Site 2)} {u a b f g : Site 2}
    (c : G.Walk u u) (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ z ∈ H.support, z = a ∨ z = b ∨ z ∉ c.support)
    (hfgC : s(f, g) ∈ c.edges) (hfa : f ≠ a) (hfb : f ≠ b) :
    s(f, g) ∉ H.edges := by
  intro hfgH
  have hfH := H.fst_mem_support_of_mem_edges hfgH
  have hfC := c.fst_mem_support_of_mem_edges hfgC
  rcases hclean f hfH with h | h | h
  · exact hfa h
  · exact hfb h
  · exact h hfC


theorem rlc_exteriorChord_terminalEdges_closureXor_of_arcPlacement
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b f g f' g' : Site 2}
    (c : G.Walk u u) (hc : c.IsTrail)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hR : s(f, g) ∈ (rlc_orderedContourArc c ha hb).edges)
    (hL : s(f', g') ∈ (rlc_complementaryContourArc c ha hb).edges)
    (hRH : s(f, g) ∉ H.edges) (hLH : s(f', g') ∉ H.edges) :
    (s(f, g) ∈
          (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse).edges ∧
        s(f', g') ∉
          (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse).edges) ∧
      (s(f, g) ∉
          (H.append ((rlc_complementaryContourArc c ha hb).mapLe
            hG).reverse).edges ∧
        s(f', g') ∈
          (H.append ((rlc_complementaryContourArc c ha hb).mapLe
            hG).reverse).edges) := by
  have hdis := rlc_orderedContourArc_edges_disjoint_complementary
    c hc ha hb
  have hRnotL : s(f, g) ∉
      (rlc_complementaryContourArc c ha hb).edges := fun h => hdis hR h
  have hLnotR : s(f', g') ∉
      (rlc_orderedContourArc c ha hb).edges := fun h => hdis h hL
  simp only [SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_reverse,
    SimpleGraph.Walk.edges_mapLe_eq_edges]
  tauto


theorem rlc_exteriorChord_rayCount_sum
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b : Site 2} (c : G.Walk u u)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (p : (hypercubicLattice 2).Walk a b) (z : Site 2) :
    jec_rayCount z
        (p.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse) +
      jec_rayCount z
        (p.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse) =
      2 * jec_rayCount z p + jec_rayCount z (c.mapLe hG) := by
  have hcArcs : jec_rayCount z (c.mapLe hG) =
      jec_rayCount z ((rlc_orderedContourArc c ha hb).mapLe hG) +
        jec_rayCount z ((rlc_complementaryContourArc c ha hb).mapLe hG) := by
    classical
    simp only [jec_rayCount, SimpleGraph.Walk.edges_mapLe_eq_edges]
    rw [← List.countP_append]
    have hperm : List.Perm
        ((rlc_orderedContourArc c ha hb).edges ++
          (rlc_complementaryContourArc c ha hb).edges) c.edges := by
      have hrot := (SimpleGraph.Walk.rotate_edges c a ha).perm
      rw [rlc_contourContactArcs_edges_decompose c ha hb] at hrot
      simpa using (List.Perm.trans
        (List.Perm.append_left _ (List.reverse_perm _)) hrot)
    exact List.Perm.countP_eq _ hperm.symm
  rw [jec_rayCount_append, jec_rayCount_append,
    jec_rayCount_reverse, jec_rayCount_reverse, hcArcs]
  omega


theorem rlc_exteriorChord_leftRegion_xor
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b : Site 2} (c : G.Walk u u)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (p : (hypercubicLattice 2).Walk a b) (z : Site 2) :
    z ∈ jec_leftRegion (c.mapLe hG) ↔
      (z ∈ jec_leftRegion
          (p.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse) ↔
        z ∉ jec_leftRegion
          (p.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse)) := by
  let C₁ := p.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse
  let C₂ := p.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse
  have hsum := rlc_exteriorChord_rayCount_sum hG c ha hb p z
  have htwice : Even (2 * jec_rayCount z p) := by
    refine ⟨jec_rayCount z p, ?_⟩
    omega
  have hparity : Even (jec_rayCount z C₁ + jec_rayCount z C₂) ↔
      Even (jec_rayCount z (c.mapLe hG)) := by
    rw [hsum, Nat.even_add]
    simp [htwice]
  simp only [jec_mem_leftRegion]
  constructor
  · intro hcOdd
    have hsumOdd : ¬Even (jec_rayCount z C₁ + jec_rayCount z C₂) :=
      fun h => hcOdd (hparity.mp h)
    have hdiff : ¬(Even (jec_rayCount z C₁) ↔
        Even (jec_rayCount z C₂)) := by
      intro hsame
      exact hsumOdd (Nat.even_add.mpr hsame)
    tauto
  · intro hdiff hcEven
    have hsumEven : Even (jec_rayCount z C₁ + jec_rayCount z C₂) :=
      hparity.mpr hcEven
    have hsame := Nat.even_add.mp hsumEven
    tauto


theorem rlc_exteriorChord_one_closure_separates_inside_outside
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b x y : Site 2} (c : G.Walk u u)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (p : (hypercubicLattice 2).Walk a b)
    (hx : x ∈ jec_leftRegion (c.mapLe hG))
    (hy : y ∉ jec_leftRegion (c.mapLe hG)) :
    rlc_OppositeLoopSides
        (p.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse)
        x y ∨
      rlc_OppositeLoopSides
        (p.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse)
        x y := by
  have hxXor :=
    (rlc_exteriorChord_leftRegion_xor hG c ha hb p x).mp hx
  have hySame :
      (y ∈ jec_leftRegion
          (p.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse)) ↔
        y ∈ jec_leftRegion
          (p.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse) := by
    have hyNotXor : ¬(
        (y ∈ jec_leftRegion
            (p.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse)) ↔
          y ∉ jec_leftRegion
            (p.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse)) := by
      intro h
      exact hy ((rlc_exteriorChord_leftRegion_xor hG c ha hb p y).mpr h)
    tauto
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor,
    rlc_oppositeLoopSides_iff_leftRegion_xor]
  tauto


theorem rlc_exteriorChord_path_meets_chord_or_orderedArc
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b x y : Site 2} (c : G.Walk u u)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (w : (hypercubicLattice 2).Walk x y)
    (hopp : rlc_OppositeLoopSides
      (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse)
      x y) :
    ∃ z ∈ w.support,
      z ∈ H.support ∨ z ∈ (rlc_orderedContourArc c ha hb).support := by
  obtain ⟨z, hzw, hzCycle⟩ :=
    rlc_closedLoop_contact_of_opposite_sides
      (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse)
      w hopp
  refine ⟨z, hzw, ?_⟩
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzCycle
  rcases hzCycle with hzH | hzArc
  · exact Or.inl hzH
  · exact Or.inr (by
      simpa [SimpleGraph.Walk.support_reverse,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzArc)


theorem rlc_exteriorChord_path_meets_chord_or_complementaryArc
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b x y : Site 2} (c : G.Walk u u)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (w : (hypercubicLattice 2).Walk x y)
    (hopp : rlc_OppositeLoopSides
      (H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse)
      x y) :
    ∃ z ∈ w.support,
      z ∈ H.support ∨
        z ∈ (rlc_complementaryContourArc c ha hb).support := by
  obtain ⟨z, hzw, hzCycle⟩ :=
    rlc_closedLoop_contact_of_opposite_sides
      (H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse)
      w hopp
  refine ⟨z, hzw, ?_⟩
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzCycle
  rcases hzCycle with hzH | hzArc
  · exact Or.inl hzH
  · exact Or.inr (by
      simpa [SimpleGraph.Walk.support_reverse,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzArc)


theorem rlc_exteriorChord_path_meets_chord_of_separatingClosure_avoidance
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b x y : Site 2} (c : G.Walk u u)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (w : (hypercubicLattice 2).Walk x y)
    (hsep :
      (rlc_OppositeLoopSides
          (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse)
          x y ∧
        ∀ z ∈ w.support,
          z ∉ (rlc_orderedContourArc c ha hb).support) ∨
      (rlc_OppositeLoopSides
          (H.append
            ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse)
          x y ∧
        ∀ z ∈ w.support,
          z ∉ (rlc_complementaryContourArc c ha hb).support)) :
    ∃ z ∈ w.support, z ∈ H.support := by
  rcases hsep with ⟨hopp, havoid⟩ | ⟨hopp, havoid⟩
  · rcases rlc_exteriorChord_path_meets_chord_or_orderedArc
        hG c ha hb H w hopp with ⟨z, hzw, hzH | hzArc⟩
    · exact ⟨z, hzw, hzH⟩
    · exact False.elim ((havoid z hzw) hzArc)
  · rcases rlc_exteriorChord_path_meets_chord_or_complementaryArc
        hG c ha hb H w hopp with ⟨z, hzw, hzH | hzArc⟩
    · exact ⟨z, hzw, hzH⟩
    · exact False.elim ((havoid z hzw) hzArc)


theorem
    rlc_exteriorChord_terminalFlankPath_meets_chord_of_closureEdgeXor
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b f g f' g' p q p' q' : Site 2}
    (c : G.Walk u u) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfg' : (hypercubicLattice 2).Adj f' g')
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hshared' : sharedPrimalEdge f' g' = s(p', q'))
    (Q : (hypercubicLattice 2).Walk q q')
    (W : (hypercubicLattice 2).Walk p p')
    (hQW : Q.support ⊆ W.support)
    (hselected :
      ((H.append
          ((rlc_orderedContourArc c ha hb).mapLe hG).reverse).IsCycle ∧
        ((s(f, g) ∈
              (H.append ((rlc_orderedContourArc c ha hb).mapLe
                hG).reverse).edges ∧
            s(f', g') ∉
              (H.append ((rlc_orderedContourArc c ha hb).mapLe
                hG).reverse).edges) ∨
          (s(f, g) ∉
              (H.append ((rlc_orderedContourArc c ha hb).mapLe
                hG).reverse).edges ∧
            s(f', g') ∈
              (H.append ((rlc_orderedContourArc c ha hb).mapLe
                hG).reverse).edges)) ∧
        ∀ z ∈ W.support,
          z ∉ (rlc_orderedContourArc c ha hb).support) ∨
      ((H.append
          ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse).IsCycle ∧
        ((s(f, g) ∈
              (H.append ((rlc_complementaryContourArc c ha hb).mapLe
                hG).reverse).edges ∧
            s(f', g') ∉
              (H.append ((rlc_complementaryContourArc c ha hb).mapLe
                hG).reverse).edges) ∨
          (s(f, g) ∉
              (H.append ((rlc_complementaryContourArc c ha hb).mapLe
                hG).reverse).edges ∧
            s(f', g') ∈
              (H.append ((rlc_complementaryContourArc c ha hb).mapLe
                hG).reverse).edges)) ∧
        ∀ z ∈ W.support,
          z ∉ (rlc_complementaryContourArc c ha hb).support)) :
    ∃ z ∈ W.support, z ∈ H.support := by
  by_cases hcontact : ∃ z ∈ W.support, z ∈ H.support
  · exact hcontact
  push Not at hcontact
  rcases hselected with ⟨hcycle, hedges, havoid⟩ |
      ⟨hcycle, hedges, havoid⟩
  · let C := H.append
      ((rlc_orderedContourArc c ha hb).mapLe hG).reverse
    have hQoff : ∀ z ∈ Q.support, z ∉ C.support := by
      intro z hzQ hzC
      rw [SimpleGraph.Walk.mem_support_append_iff] at hzC
      rcases hzC with hzH | hzArc
      · exact hcontact z (hQW hzQ) hzH
      · exact (havoid z (hQW hzQ)) (by
          simpa [SimpleGraph.Walk.support_reverse,
            SimpleGraph.Walk.support_mapLe_eq_support] using hzArc)
    have hopp := rlc_two_terminalFlanks_oppositeLoopSides_of_edgeXor
      C hcycle.edges_nodup hfg hfg' hpq hpq' hshared hshared'
        Q hQoff (by simpa [C] using hedges)
    exact rlc_exteriorChord_path_meets_chord_of_separatingClosure_avoidance
      hG c ha hb H W (Or.inl ⟨by simpa [C] using hopp, havoid⟩)
  · let C := H.append
      ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse
    have hQoff : ∀ z ∈ Q.support, z ∉ C.support := by
      intro z hzQ hzC
      rw [SimpleGraph.Walk.mem_support_append_iff] at hzC
      rcases hzC with hzH | hzArc
      · exact hcontact z (hQW hzQ) hzH
      · exact (havoid z (hQW hzQ)) (by
          simpa [SimpleGraph.Walk.support_reverse,
            SimpleGraph.Walk.support_mapLe_eq_support] using hzArc)
    have hopp := rlc_two_terminalFlanks_oppositeLoopSides_of_edgeXor
      C hcycle.edges_nodup hfg hfg' hpq hpq' hshared hshared'
        Q hQoff (by simpa [C] using hedges)
    exact rlc_exteriorChord_path_meets_chord_of_separatingClosure_avoidance
      hG c ha hb H W (Or.inr ⟨by simpa [C] using hopp, havoid⟩)


theorem rlc_exteriorChord_inside_to_outside_path_meets_chord_or_cycleArc
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b x y : Site 2} (c : G.Walk u u)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (w : (hypercubicLattice 2).Walk x y)
    (hx : x ∈ jec_leftRegion (c.mapLe hG))
    (hy : y ∉ jec_leftRegion (c.mapLe hG)) :
    (∃ z ∈ w.support,
        z ∈ H.support ∨ z ∈ (rlc_orderedContourArc c ha hb).support) ∨
      ∃ z ∈ w.support,
        z ∈ H.support ∨
          z ∈ (rlc_complementaryContourArc c ha hb).support := by
  rcases rlc_exteriorChord_one_closure_separates_inside_outside
      hG c ha hb H hx hy with hordered | hcomplementary
  · exact Or.inl
      (rlc_exteriorChord_path_meets_chord_or_orderedArc
        hG c ha hb H w hordered)
  · exact Or.inr
      (rlc_exteriorChord_path_meets_chord_or_complementaryArc
        hG c ha hb H w hcomplementary)


theorem rlc_exteriorChord_inside_to_outside_path_meets_chord_of_avoids_cycle
    {G : SimpleGraph (Site 2)} (hG : G ≤ hypercubicLattice 2)
    {u a b x y : Site 2} (c : G.Walk u u)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (w : (hypercubicLattice 2).Walk x y)
    (hx : x ∈ jec_leftRegion (c.mapLe hG))
    (hy : y ∉ jec_leftRegion (c.mapLe hG))
    (havoid : ∀ z ∈ w.support, z ∉ c.support) :
    ∃ z ∈ w.support, z ∈ H.support := by
  rcases rlc_exteriorChord_inside_to_outside_path_meets_chord_or_cycleArc
      hG c ha hb H w hx hy with
    ⟨z, hzw, hzH | hzArc⟩ | ⟨z, hzw, hzH | hzArc⟩
  · exact ⟨z, hzw, hzH⟩
  · exact False.elim ((havoid z hzw)
      (rlc_orderedContourArc_support_subset c ha hb hzArc))
  · exact ⟨z, hzw, hzH⟩
  · exact False.elim ((havoid z hzw)
      (rlc_complementaryContourArc_support_subset c ha hb hzArc))


theorem
    rlc_twoChannelFullPhysical_insideOutsideEdge_meets_exteriorChord_or_cycleArc
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    (∃ z ∈ hpq.toWalk.support,
        z ∈ H.support ∨ z ∈ (rlc_orderedContourArc c ha hb).support) ∨
      ∃ z ∈ hpq.toWalk.support,
        z ∈ H.support ∨
          z ∈ (rlc_complementaryContourArc c ha hb).support := by
  have hpInside : p ∈ jec_leftRegion
      (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle]
    exact rlc_twoChannelFullReachSet_subset_filled
      gamma gamma' omega hpReach
  have hqOutside : q ∉ jec_leftRegion
      (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle]
    exact hqOut
  exact rlc_exteriorChord_inside_to_outside_path_meets_chord_or_cycleArc
    (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
    c ha hb H hpq.toWalk hpInside hqOutside


theorem
    rlc_twoChannelFullPhysical_insideOutsideEdge_endpointContact_cases
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    (p ∈ H.support ∨ q ∈ H.support ∨
        p ∈ (rlc_orderedContourArc c ha hb).support ∨
        q ∈ (rlc_orderedContourArc c ha hb).support) ∨
      (p ∈ H.support ∨ q ∈ H.support ∨
        p ∈ (rlc_complementaryContourArc c ha hb).support ∨
        q ∈ (rlc_complementaryContourArc c ha hb).support) := by
  rcases
      rlc_twoChannelFullPhysical_insideOutsideEdge_meets_exteriorChord_or_cycleArc
        c hcycle ha hb H hpq hpReach hqOut with
      ⟨z, hzEdge, hzH | hzArc⟩ | ⟨z, hzEdge, hzH | hzArc⟩
  · have hz : z = p ∨ z = q := by
      simpa [SimpleGraph.Adj.toWalk] using hzEdge
    rcases hz with rfl | rfl
    · exact Or.inl (Or.inl hzH)
    · exact Or.inl (Or.inr (Or.inl hzH))
  · have hz : z = p ∨ z = q := by
      simpa [SimpleGraph.Adj.toWalk] using hzEdge
    rcases hz with rfl | rfl
    · exact Or.inl (Or.inr (Or.inr (Or.inl hzArc)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr hzArc)))
  · have hz : z = p ∨ z = q := by
      simpa [SimpleGraph.Adj.toWalk] using hzEdge
    rcases hz with rfl | rfl
    · exact Or.inr (Or.inl hzH)
    · exact Or.inr (Or.inr (Or.inl hzH))
  · have hz : z = p ∨ z = q := by
      simpa [SimpleGraph.Adj.toWalk] using hzEdge
    rcases hz with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl hzArc)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hzArc)))


theorem
    rlc_twoChannelFullPhysical_insideOutsideEdge_meets_exteriorChord_of_avoidsCycle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (havoid : p ∉ c.support ∧ q ∉ c.support) :
    p ∈ H.support ∨ q ∈ H.support := by
  have hpInside : p ∈ jec_leftRegion
      (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle]
    exact rlc_twoChannelFullReachSet_subset_filled
      gamma gamma' omega hpReach
  have hqOutside : q ∉ jec_leftRegion
      (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle]
    exact hqOut
  obtain ⟨z, hzEdge, hzH⟩ :=
    rlc_exteriorChord_inside_to_outside_path_meets_chord_of_avoids_cycle
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
      c ha hb H hpq.toWalk hpInside hqOutside (by
        intro z hz
        have hzCases : z = p ∨ z = q := by
          simpa [SimpleGraph.Adj.toWalk] using hz
        rcases hzCases with rfl | rfl
        · exact havoid.1
        · exact havoid.2)
  have hzCases : z = p ∨ z = q := by
    simpa [SimpleGraph.Adj.toWalk] using hzEdge
  rcases hzCases with rfl | rfl
  · exact Or.inl hzH
  · exact Or.inr hzH


theorem rlc_bookPhysicalTraceNetworkBracket_contactPlacement
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {r s u : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hstart : rlc_dualReflect.symm r ∈ c.support)
    (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support) :
    let B := rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs
    let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
    let k := B.support.idxOf d
    ∃ i j j' : Nat,
      i < k ∧ k < j ∧ j ≤ j' ∧ j' ≤ B.length ∧
        B.getVert i ∈ c.support ∧ B.getVert j ∈ c.support ∧
        B.getVert j' ∈ c.support ∧ B.getVert k = d ∧
        (∀ l : Nat, i < l → l < j → B.getVert l ∉ c.support) ∧
        (∀ l : Nat, i < l → l < j →
          B.getVert l ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∧
        rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect (B.getVert j') ∈ rlc_pathVertices gamma'.1 ∧
        B.getVert i ≠ B.getVert j' ∧
        (j' = j ∨
          (B.getVert j = rlc_dualReflect.symm
              (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) ∧
            j < j' ∧
            ∀ l : Nat, j < l → l < j' →
              B.getVert l ∉ c.support)) := by
  dsimp only
  obtain ⟨i, j, hik, hkj, hjLength, hi, hj, hkGet, hbetween,
      hside, hiRight, hjGood⟩ :=
    rlc_bookPhysicalTraceNetworkBracket_ordered_contactExtrema
      hn gamma gamma' hfaith omega hr hs hsLeft hrs
        c hcycle hstart hend
  rcases hjGood with hjLeft | hjCollar
  · have hijNe :
        (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i ≠
          (rlc_bookPhysicalTraceNetworkBracket
            gamma gamma' hr hs hsLeft hrs).getVert j := by
      intro hij
      exact hfaith.traceVertices_disjoint hiRight (by
        simpa [← hij] using hjLeft)
    exact ⟨i, j, j, hik, hkj, le_rfl, hjLength, hi, hj, hj,
      hkGet, hbetween, hside, hiRight, hjLeft, hijNe, Or.inl rfl⟩
  · obtain ⟨j', hjj', hj'Length, hj'Contact, hj'Left, hbetween'⟩ :=
      rlc_bookPhysicalTraceNetworkBracket_next_left_after_collar
        hn gamma gamma' hfaith omega hr hs hsLeft hrs c hcycle hend
          hjLength hkj hjCollar
    have hijNe :
        (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i ≠
          (rlc_bookPhysicalTraceNetworkBracket
            gamma gamma' hr hs hsLeft hrs).getVert j' := by
      intro hij
      exact hfaith.traceVertices_disjoint hiRight (by
        simpa [← hij] using hj'Left)
    exact ⟨i, j, j', hik, hkj, Nat.le_of_lt hjj', hj'Length,
      hi, hj, hj'Contact, hkGet, hbetween, hside, hiRight, hj'Left,
      hijNe, Or.inr ⟨hjCollar, hjj', hbetween'⟩⟩


theorem rlc_bookPhysicalTraceNetworkBracket_exteriorChord
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {r s u : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hstart : rlc_dualReflect.symm r ∈ c.support)
    (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support) :
    let B := rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs
    let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
    let k := B.support.idxOf d
    ∃ (i j j' : Nat)
      (H : (hypercubicLattice 2).Walk (B.getVert i) (B.getVert j)),
      H.IsPath ∧ i < k ∧ k < j ∧ j ≤ j' ∧ j' ≤ B.length ∧
        B.getVert i ∈ c.support ∧ B.getVert j ∈ c.support ∧
        B.getVert j' ∈ c.support ∧
        rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect (B.getVert j') ∈ rlc_pathVertices gamma'.1 ∧
        B.getVert i ≠ B.getVert j' ∧
        d ∈ H.support ∧
        d ∉ c.support ∧
        H.support ⊆ B.support ∧
        (∀ v ∈ H.support,
          v = B.getVert i ∨ v = B.getVert j ∨
            (v ∉ c.support ∧
              v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
                (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧
        (j' = j ∨
          (B.getVert j = rlc_dualReflect.symm
              (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) ∧
            j < j' ∧
            ∀ l : Nat, j < l → l < j' →
              B.getVert l ∉ c.support)) := by
  dsimp only
  let B := rlc_bookPhysicalTraceNetworkBracket
    gamma gamma' hr hs hsLeft hrs
  let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
  let k := B.support.idxOf d
  obtain ⟨i, j, j', hik, hkj, hjj', hj'Length, hi, hj, hj',
      hkGet, hbetween, hside, hiRight, hj'Left, hij'Ne, hjCase⟩ :=
    rlc_bookPhysicalTraceNetworkBracket_contactPlacement
      hn gamma gamma' hfaith omega hr hs hsLeft hrs
        c hcycle hstart hend
  have hj'LengthB : j' ≤ B.length := by
    simpa [B] using hj'Length
  have hiLength : i ≤ B.length := by omega
  have hij : i ≤ j := by omega
  have hjLength : j ≤ B.length := by omega
  let H := rlc_walkIndexInterval B i j hiLength hij hjLength
  have hHPath : H.IsPath := by
    dsimp only [H, rlc_walkIndexInterval]
    simpa only [SimpleGraph.Walk.isPath_copy] using
      ((rlc_bookPhysicalTraceNetworkBracket_isPath
        hn hfaith hr hs hsLeft hrs).drop i).take (j - i)
  have hdH : d ∈ H.support := by
    have hkH := rlc_walkIndexInterval_getVert_mem
      B i j hiLength hij hjLength (Nat.le_of_lt hik) (Nat.le_of_lt hkj)
    have hkGetB : B.getVert k = d := by
      simpa [B, d, k] using hkGet
    rw [← hkGetB]
    exact hkH
  have hdOff : d ∉ c.support := by
    intro hdc
    have hdBox := rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox
      hn gamma gamma' omega c hcycle hdc
    rw [mem_rect] at hdBox
    dsimp only [d] at hdBox
    simp only [rlc_dualReflect_symm_zero, Matrix.cons_val_zero] at hdBox
    omega
  have hHB : H.support ⊆ B.support := by
    intro v hv
    obtain ⟨l, _hil, _hlj, hlv⟩ :=
      rlc_walkIndexInterval_support B i j hiLength hij hjLength hv
    rw [← hlv]
    exact B.getVert_mem_support l
  refine ⟨i, j, j', H, hHPath, hik, hkj, hjj', hj'Length, hi, hj, hj',
    hiRight, hj'Left, hij'Ne, hdH, hdOff, hHB, ?_, hjCase⟩
  intro v hv
  by_cases hvi : v = B.getVert i
  · exact Or.inl hvi
  by_cases hvj : v = B.getVert j
  · exact Or.inr (Or.inl hvj)
  right
  right
  obtain ⟨l, hil, hlj, hlv⟩ :=
    rlc_walkIndexInterval_support_interior
      B i j hiLength hij hjLength hv hvi hvj
  rw [← hlv]
  exact ⟨hbetween l hil hlj, hside l hil hlj⟩


theorem rlc_bookPhysicalTraceNetworkBracket_exteriorChord_separatorCycles
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {r s u : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hstart : rlc_dualReflect.symm r ∈ c.support)
    (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support) :
    let B := rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs
    let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
    let k := B.support.idxOf d
    ∃ (i j j' : Nat)
      (H : (hypercubicLattice 2).Walk (B.getVert i) (B.getVert j))
      (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support),
      H.IsPath ∧ i < k ∧ k < j ∧ j ≤ j' ∧ j' ≤ B.length ∧
        B.getVert j' ∈ c.support ∧
        rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect (B.getVert j') ∈ rlc_pathVertices gamma'.1 ∧
        B.getVert i ≠ B.getVert j' ∧
        d ∈ H.support ∧ d ∉ c.support ∧
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
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
        (j' = j ∨
          (B.getVert j = rlc_dualReflect.symm
              (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) ∧
            j < j' ∧
            ∀ l : Nat, j < l → l < j' →
              B.getVert l ∉ c.support)) := by
  dsimp only
  let B := rlc_bookPhysicalTraceNetworkBracket
    gamma gamma' hr hs hsLeft hrs
  let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
  let k := B.support.idxOf d
  obtain ⟨i, j, j', H, hHPath, hik, hkj, hjj', hj'Length,
      hi, hj, hj', hiRight, hj'Left, hij'Ne, hdH, hdOff, hHB, hclean,
      hjCase⟩ :=
    rlc_bookPhysicalTraceNetworkBracket_exteriorChord
      hn gamma gamma' hfaith omega hr hs hsLeft hrs
        c hcycle hstart hend
  have hcycles := rlc_exteriorChord_complementaryArcCycles
    (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
    c hcycle H hHPath hi hj hdH hdOff (by
      intro v hv
      rcases hclean v hv with hvi | hvj | hoff
      · exact Or.inl hvi
      · exact Or.inr (Or.inl hvj)
      · exact Or.inr (Or.inr hoff.1))
  exact ⟨i, j, j', H, hi, hj, hHPath, hik, hkj, hjj', hj'Length,
    hj', hiRight, hj'Left, hij'Ne, hdH, hdOff, hHB, hclean,
    hcycles.1, hcycles.2, hjCase⟩


theorem rlc_bookPhysicalTraceNetworkBracket_sameContact_contactExtrema
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {r u : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hstart : rlc_dualReflect.symm r ∈ c.support)
    (hend : rlc_dualReflect.symm (rlc_flipX r) ∈ c.support) :
    let B := rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hr hrLeft le_rfl
    let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)
    let k := B.support.idxOf d
    ∃ i j : Nat,
      i < k ∧ k < j ∧ j ≤ B.length ∧
        B.getVert i ∈ c.support ∧ B.getVert j ∈ c.support ∧
        B.getVert k = d ∧
        (∀ l : Nat, i < l → l < j → B.getVert l ∉ c.support) ∧
        (∀ l : Nat, i < l → l < j →
          B.getVert l ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∧
        rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧
        (rlc_dualReflect (B.getVert j) ∈ rlc_pathVertices gamma'.1 ∨
          B.getVert j = rlc_dualReflect.symm
            (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) := by
  dsimp only
  obtain ⟨i, j, hik, hkj, hjLength, hi, hj, hkGet, hbetween,
      hside, hiRight, hjProv⟩ :=
    rlc_bookPhysicalTraceNetworkBracket_contactExtrema
      hn gamma gamma' omega hr hr hrLeft le_rfl c hcycle hstart hend
  have hjGood :
      rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hr hrLeft le_rfl).getVert j) ∈
          rlc_pathVertices gamma'.1 ∨
        (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hr hrLeft le_rfl).getVert j =
            rlc_dualReflect.symm
              (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
    rcases hjProv with hjRight | hjLeft | hjCollar
    · have hjLe :=
        rlc_bookPhysicalTraceNetworkBracket_sameContact_right_index_le_exterior
          hn hfaith hr hrLeft hjLength hjRight
      omega
    · exact Or.inl hjLeft
    · exact Or.inr hjCollar
  exact ⟨i, j, hik, hkj, hjLength, hi, hj, hkGet, hbetween,
    hside, hiRight, hjGood⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_canonicalPhysicalTraceNetworkBracket
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    ∃ (r s : Site 2)
      (hr : r ∈ rlc_pathVertices gamma.1)
      (hs : s ∈ rlc_pathVertices gamma.1)
      (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
      (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
      (Q : (hypercubicLattice 2).Walk x y),
      rlc_dualReflect.symm r = x ∧
        rlc_dualReflect.symm (rlc_flipX s) = y ∧
      Q.support = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).support ∧
        ∀ v ∈ Q.support,
          v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1) := by
  obtain ⟨r, s, _P, hrSet, hsPath, _hsFlipLeft, hxr, hys,
    hrz, hzs, _hzP, _hP⟩ := h
  have hrPath : r ∈ rlc_pathVertices gamma.1 :=
    (Finset.mem_filter.mp hrSet).1
  have hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1 := by
    rw [hys] at hyPath
    exact hyPath
  have hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s := hrz.trans hzs
  have hrx : rlc_dualReflect.symm r = x := by
    rw [← hxr]
    exact rlc_dualReflect.symm_apply_apply x
  have hsy : rlc_dualReflect.symm (rlc_flipX s) = y := by
    rw [← hys]
    exact rlc_dualReflect.symm_apply_apply y
  let B := rlc_bookPhysicalTraceNetworkBracket
    gamma gamma' hrPath hsPath hsLeft hrs
  let Q : (hypercubicLattice 2).Walk x y := B.copy hrx hsy
  refine ⟨r, s, hrPath, hsPath, hsLeft, hrs, Q, hrx, hsy, ?_, ?_⟩
  · exact SimpleGraph.Walk.support_copy _ _ _
  · intro v hv
    apply rlc_bookPhysicalTraceNetworkBracket_mem_rect
      gamma gamma' hrPath hsPath hsLeft hrs
    simpa [Q, B, SimpleGraph.Walk.support_copy] using hv


theorem rlc_bookPhysicalTraceNetworkBracket_support_cases
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {r s v : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hv : v ∈ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support) :
    (∃ w ∈ rlc_pathVertices gamma.1,
        v = rlc_dualReflect.symm w) ∨
      (∃ w ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support,
        v = rlc_dualReflect.symm w) ∨
      ∃ w ∈ rlc_pathVertices gamma'.1,
        v = rlc_dualReflect.symm w := by
  change v ∈ ((rlc_bookTraceNetworkBracket
    gamma gamma' hr hs hsLeft hrs).map
      rlc_dualReflectSymmLatticeHom).support at hv
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
  obtain ⟨w, hw, hwv⟩ := hv
  have hvw : v = rlc_dualReflect.symm w := hwv.symm
  change w ∈ ((rlc_rightAmbientTraceCanonicalSegment
    gamma hr hs hrs).append
      (rlc_bookOuterTraceNetworkArc gamma gamma' hs hsLeft)).support at hw
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hwSegment | hwOuter
  · exact Or.inl ⟨w,
      rlc_rightAmbientTraceCanonicalSegment_support_path
        gamma hr hs hrs hwSegment, hvw⟩
  · rcases rlc_bookOuterTraceNetworkArc_support_cases
        gamma gamma' hs hsLeft hwOuter with hwRight | hwDetour | hwLeft
    · have hwAmbient :=
        (rlc_ambientCrossingWalk gamma.1).support_dropUntil_subset
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma.1 s).2 hs) hwRight
      exact Or.inl ⟨w,
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma.1 w).1 hwAmbient, hvw⟩
    · exact Or.inr (Or.inl ⟨w, hwDetour, hvw⟩)
    · have hwAmbient :=
        (rlc_ambientCrossingWalk gamma'.1).support_takeUntil_subset_support
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma'.1 (rlc_flipX s)).2 hsLeft) hwLeft
      exact Or.inr (Or.inr ⟨w,
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 w).1 hwAmbient, hvw⟩)


theorem rlc_bookPhysicalTraceNetworkBracket_shiftedSource_cases
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {r s a : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (haBox : a ∈ rect (-2 * n) (2 * n) (-n) n)
    (haBracket : phb_doubleDualShift a ∈
      (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).support) :
    (∃ w ∈ rlc_pathVertices gamma.1, a = rlc_flipX w) ∨
      ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w := by
  rcases rlc_bookPhysicalTraceNetworkBracket_support_cases
      gamma gamma' hr hs hsLeft hrs haBracket with
    ⟨w, hwRight, hshift⟩ | ⟨w, hwDetour, hshift⟩ |
      ⟨w, hwLeft, hshift⟩
  · left
    exact ⟨w, hwRight,
      (rlc_doubleDualShift_eq_dualReflect_symm_iff a w).1 hshift⟩
  · have haw : a = rlc_flipX w :=
      (rlc_doubleDualShift_eq_dualReflect_symm_iff a w).1 hshift
    have hwBox : w ∈ rect (-2 * n) (2 * n) (-n) n := by
      rw [haw] at haBox
      exact (rlc_mem_connectorBox_flipX w).mpr haBox
    by_cases hw0 : 0 ≤ w 0
    · have hwRightBox : w ∈ rect 0 (2 * n) (-n) n := by
        rw [mem_rect] at hwBox ⊢
        omega
      have hwEnd :=
        rlc_bookExteriorEndpointDetour_meets_rightBox_only_endpoint
          hn gamma gamma' hwDetour hwRightBox
      left
      refine ⟨w, ?_, haw⟩
      rw [hwEnd]
      exact rlc_connector_path_end_mem_vertices gamma.1
    · have hwLeftBox : w ∈ rect (-2 * n) 0 (-n) n := by
        rw [mem_rect] at hwBox ⊢
        omega
      have hwStart :=
        rlc_bookExteriorEndpointDetour_meets_leftBox_only_endpoint
          hn gamma gamma' hwDetour hwLeftBox
      right
      refine ⟨w, ?_, haw⟩
      rw [hwStart]
      exact rlc_path_start_mem_vertices gamma'.1
  · right
    exact ⟨w, hwLeft,
      (rlc_doubleDualShift_eq_dualReflect_symm_iff a w).1 hshift⟩


theorem rlc_twoChannelFullPhysical_shiftedReach_bracket_cases
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {r s a : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (haBracket : phb_doubleDualShift a ∈
      (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).support) :
    (∃ w ∈ rlc_pathVertices gamma.1, a = rlc_flipX w) ∨
      ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w := by
  apply rlc_bookPhysicalTraceNetworkBracket_shiftedSource_cases
    hn gamma gamma' hr hs hsLeft hrs
  · exact rlc_twoChannelFullReachSet_subset_box gamma gamma' omega haReach
  · exact haBracket


theorem
    rlc_twoChannelFullPhysical_reachable_reflectedRight_axis_or_exclusive
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {a w : Site 2}
    (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hwRight : w ∈ rlc_pathVertices gamma.1)
    (haw : a = rlc_flipX w) :
    a = (gamma.1.1 : Site 2) ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' a := by
  by_cases haRight : a ∈ rlc_pathVertices gamma.1
  · left
    have hwBox := rlc_pathVertex_mem_rect gamma.1 hwRight
    have haBox := rlc_pathVertex_mem_rect gamma.1 haRight
    have hw0 : w 0 = 0 := by
      rw [mem_rect] at hwBox haBox
      have hcoord : a 0 = -w 0 := by
        rw [haw]
        rfl
      omega
    have hwAxis := hfaith.right_axis_unique hwRight hw0
    rw [haw, hwAxis]
    exact rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  · right
    have haLeft : a ∉ rlc_pathVertices gamma'.1 := by
      intro haLeft
      exact (rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
        gamma gamma' omega hno haLeft) haReach
    have haNeg : a 0 < 0 := by
      have hwBox := rlc_pathVertex_mem_rect gamma.1 hwRight
      rw [mem_rect] at hwBox
      have hcoord : a 0 = -w 0 := by
        rw [haw]
        rfl
      by_contra hnot
      have hw0 : w 0 = 0 := by omega
      have hwAxis := hfaith.right_axis_unique hwRight hw0
      apply haRight
      rw [haw, hwAxis]
      rw [rlc_flipX_eq_self_of_zero gamma.1.1.2.2]
      exact rlc_path_start_mem_vertices gamma.1
    exact ⟨haNeg, ⟨w, hwRight, haw⟩, haRight, haLeft⟩


theorem rlc_doubleDualShift_leftRegion_iff_of_shortRoute_offLoop
    {u a : Site 2} (C : (hypercubicLattice 2).Walk u u)
    (ha : a ∉ C.support)
    (hwest : (![a 0 - 1, a 1] : Site 2) ∉ C.support)
    (hshift : phb_doubleDualShift a ∉ C.support) :
    a ∈ jec_leftRegion C ↔ phb_doubleDualShift a ∈ jec_leftRegion C := by
  let west : Site 2 := ![a 0 - 1, a 1]
  have haWest : (hypercubicLattice 2).Adj a west := by
    simp [west, hypercubicLattice_adj, Fin.sum_univ_two]
  have hwestShift : (hypercubicLattice 2).Adj west
      (phb_doubleDualShift a) := by
    simp [west, phb_doubleDualShift, hypercubicLattice_adj,
      Fin.sum_univ_two]
  have hparity := (jec_localConstancy C haWest ha (by simpa [west] using hwest)).trans
    (jec_localConstancy C hwestShift (by simpa [west] using hwest) hshift)
  simpa only [jec_mem_leftRegion] using not_congr hparity


theorem rlc_oppositeLoopSides_doubleDualShift_of_shortRoutes_offLoop
    {u p q : Site 2} (C : (hypercubicLattice 2).Walk u u)
    (hopp : rlc_OppositeLoopSides C p q)
    (hp : p ∉ C.support)
    (hpWest : (![p 0 - 1, p 1] : Site 2) ∉ C.support)
    (hpShift : phb_doubleDualShift p ∉ C.support)
    (hq : q ∉ C.support)
    (hqWest : (![q 0 - 1, q 1] : Site 2) ∉ C.support)
    (hqShift : phb_doubleDualShift q ∉ C.support) :
    rlc_OppositeLoopSides C
      (phb_doubleDualShift p) (phb_doubleDualShift q) := by
  have hpSide :=
    rlc_doubleDualShift_leftRegion_iff_of_shortRoute_offLoop
      C hp hpWest hpShift
  have hqSide :=
    rlc_doubleDualShift_leftRegion_iff_of_shortRoute_offLoop
      C hq hqWest hqShift
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor] at hopp ⊢
  rw [← hpSide, ← hqSide]
  exact hopp


theorem rlc_doubleDualShift_oppositeSides_or_shortRoute_contact
    {u p q : Site 2} (C : (hypercubicLattice 2).Walk u u)
    (hopp : rlc_OppositeLoopSides C p q) :
    rlc_OppositeLoopSides C
        (phb_doubleDualShift p) (phb_doubleDualShift q) ∨
      ∃ z ∈ C.support,
        z = p ∨ z = ![p 0 - 1, p 1] ∨
          z = phb_doubleDualShift p ∨ z = q ∨
          z = ![q 0 - 1, q 1] ∨
          z = phb_doubleDualShift q := by
  by_cases hp : p ∈ C.support
  · exact Or.inr ⟨p, hp, Or.inl rfl⟩
  by_cases hpWest : (![p 0 - 1, p 1] : Site 2) ∈ C.support
  · exact Or.inr ⟨![p 0 - 1, p 1], hpWest, Or.inr (Or.inl rfl)⟩
  by_cases hpShift : phb_doubleDualShift p ∈ C.support
  · exact Or.inr ⟨phb_doubleDualShift p, hpShift,
      Or.inr (Or.inr (Or.inl rfl))⟩
  by_cases hq : q ∈ C.support
  · exact Or.inr ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  by_cases hqWest : (![q 0 - 1, q 1] : Site 2) ∈ C.support
  · exact Or.inr ⟨![q 0 - 1, q 1], hqWest,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  by_cases hqShift : phb_doubleDualShift q ∈ C.support
  · exact Or.inr ⟨phb_doubleDualShift q, hqShift,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
  exact Or.inl
    (rlc_oppositeLoopSides_doubleDualShift_of_shortRoutes_offLoop
      C hopp hp hpWest hpShift hq hqWest hqShift)


theorem rlc_twoChannelFullPhysical_shiftedReach_shortBoundaryContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hshiftOutside : phb_doubleDualShift a ∉
      jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))
    (hshiftOffCycle : phb_doubleDualShift a ∉ c.support) :
    a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support := by
  let C := c.mapLe (faceBoundaryGraph_le
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
  let L := sw_lshape (a 0) (a 1) (a 0 - 1) (a 1 - 1)
  have hregion :=
    rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle
  have haInside : a ∈ jec_leftRegion C := by
    rw [← hregion]
    exact rlc_twoChannelFullReachSet_subset_filled
      gamma gamma' omega haReach
  have hstart : (![a 0, a 1] : Site 2) = a := by
    ext i
    fin_cases i <;> simp
  have hend : (![a 0 - 1, a 1 - 1] : Site 2) =
      phb_doubleDualShift a := by
    ext i
    fin_cases i <;> simp [phb_doubleDualShift]
  have hopposite : rlc_OppositeLoopSides C
      (![a 0, a 1] : Site 2) ![a 0 - 1, a 1 - 1] := by
    right
    constructor
    · simpa [hstart, jec_mem_leftRegion] using haInside
    · simpa [hend, C, jec_mem_leftRegion] using hshiftOutside
  obtain ⟨z, hzL, hzC⟩ :=
    rlc_closedLoop_contact_of_opposite_sides C L hopposite
  have hzCycle : z ∈ c.support := by
    simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hzC
  dsimp only [L] at hzL
  rw [sw_lshape_mem_support] at hzL
  rcases hzL with hzHoriz | hzVert
  · rw [sw_horizSeg_mem_support] at hzHoriz
    obtain ⟨t, ht, rfl⟩ := hzHoriz
    rw [Set.mem_uIcc] at ht
    rcases ht with ht | ht
    · by_cases hta : t = a 0
      · left
        have heq : (![t, a 1] : Site 2) = a := by
          ext i
          fin_cases i <;> simp [hta]
        simpa [heq] using hzCycle
      · right
        have hta' : t = a 0 - 1 := by omega
        simpa [hta'] using hzCycle
    · by_cases hta : t = a 0
      · left
        have heq : (![t, a 1] : Site 2) = a := by
          ext i
          fin_cases i <;> simp [hta]
        simpa [heq] using hzCycle
      · right
        have hta' : t = a 0 - 1 := by omega
        simpa [hta'] using hzCycle
  · rw [sw_vertSeg_mem_support] at hzVert
    obtain ⟨t, ht, rfl⟩ := hzVert
    rw [Set.mem_uIcc] at ht
    rcases ht with ht | ht
    · by_cases hta : t = a 1
      · right
        simpa [hta] using hzCycle
      · have hta' : t = a 1 - 1 := by omega
        exact False.elim (hshiftOffCycle (by simpa [hend, hta'] using hzCycle))
    · by_cases hta : t = a 1
      · right
        simpa [hta] using hzCycle
      · have hta' : t = a 1 - 1 := by omega
        exact False.elim (hshiftOffCycle (by simpa [hend, hta'] using hzCycle))


theorem
    rlc_twoChannelFullPhysical_shiftedReach_shortRoute_boundaryEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hshiftOutside : phb_doubleDualShift a ∉
      jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) :
    ∃ p q f g : Site 2,
      s(p, q) ∈
          (sw_lshape (a 0) (a 1) (a 0 - 1) (a 1 - 1)).edges ∧
        p ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        sharedPrimalEdge f g = s(p, q) ∧
        s(f, g) ∈ c.edges ∧
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph
            gamma gamma' omega).Adj f g ∨
          ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' f g) := by
  let K := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  have hstart : (![a 0, a 1] : Site 2) = a := by
    ext i
    fin_cases i <;> simp
  have hend : (![a 0 - 1, a 1 - 1] : Site 2) =
      phb_doubleDualShift a := by
    ext i
    fin_cases i <;> simp [phb_doubleDualShift]
  let L : (hypercubicLattice 2).Walk a (phb_doubleDualShift a) :=
    (sw_lshape (a 0) (a 1) (a 0 - 1) (a 1 - 1)).copy hstart hend
  have haK : a ∈ K :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega haReach
  have hshiftK : phb_doubleDualShift a ∉ K := by
    intro hshift
    apply hshiftOutside
    rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle]
    exact hshift
  obtain ⟨p, q, hpq, hpK, hqK⟩ :=
    rlc_walk_pred_first_exit L (fun z => z ∈ K) haK hshiftK
  have hpqAdj : (hypercubicLattice 2).Adj p q :=
    L.adj_of_mem_edges hpq
  obtain ⟨f, g, hflank, hfgAdj⟩ := flankFaces_latAdj hpqAdj
  have hshared : sharedPrimalEdge f g = s(p, q) := by
    have hsps : symPrimalSym (flankFaces p q) = s(p, q) :=
      symPrimalSym_flankFaces hpqAdj
    rw [← symPrimal_eq_shared hfgAdj, ← symPrimalSym_mk,
      ← hflank, hsps]
  have hfgBoundary : (faceBoundaryGraph K).Adj f g := by
    rw [faceBoundaryGraph_adj]
    refine ⟨hfgAdj, ?_⟩
    rw [hshared, bdEdge_mk]
    exact ⟨fun _ => hqK, fun _ => hpK⟩
  have hcNotNil : ¬c.Nil := by
    intro hnil
    exact hcycle.ne_nil hnil.eq_nil
  have huSupport : u ∈ (faceBoundaryGraph K).support :=
    (c.adj_snd hcNotNil).mem_support_left
  have hfgCycle : s(f, g) ∈ c.edges :=
    rlc_twoChannelFullPhysical_contactCycle_covers
      gamma gamma' omega c hcycle huSupport c.start_mem_support
        s(f, g) hfgBoundary
  refine ⟨p, q, f, g, ?_⟩
  have hpqL : s(p, q) ∈
      (sw_lshape (a 0) (a 1) (a 0 - 1) (a 1 - 1)).edges := by
    simpa [L, SimpleGraph.Walk.edges_copy] using hpq
  refine ⟨hpqL, hpK, hqK, hshared, hfgCycle, ?_⟩
  by_cases hcarrier :
      RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g
  · exact Or.inl
      ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).2 ⟨hfgBoundary, hcarrier⟩)
  · exact Or.inr hcarrier


theorem rlc_twoChannelFullPhysical_shiftedReach_inside_or_shortBoundaryContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hshiftOffCycle : phb_doubleDualShift a ∉ c.support) :
    phb_doubleDualShift a ∈
        jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∨
      a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support := by
  by_cases hinside : phb_doubleDualShift a ∈
      jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))
  · exact Or.inl hinside
  · exact Or.inr
      (rlc_twoChannelFullPhysical_shiftedReach_shortBoundaryContact
        c hcycle haReach hinside hshiftOffCycle)


theorem
    rlc_twoChannelFullPhysical_sourceSplice_offContour_inside_or_tetherContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u ur vr ul vl s t : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (T : (hypercubicLattice 2).Walk s t)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift r = v)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    {v : Site 2} (hvT : v ∈ T.support) (hvOff : v ∉ c.support) :
    v ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∨
      ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
        phb_doubleDualShift r = v ∧
          (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) := by
  have huGraph : u ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support :=
    by
      have hcNotNil : ¬c.Nil := by
        intro hnil
        exact hcycle.ne_nil hnil.eq_nil
      have huCycle := c.start_mem_support
      rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
        hcNotNil] at huCycle
      obtain ⟨e, he, hue⟩ := huCycle
      induction e using Sym2.inductionOn with
      | _ a b =>
          have hab := c.adj_of_mem_edges he
          rw [Sym2.mem_iff] at hue
          rcases hue with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hab.mem_support_left
          · exact hab.mem_support_right
  have hurvCycle : s(ur, vr) ∈ c.edges :=
    rlc_twoChannelFullPhysical_contactCycle_covers
      gamma gamma' omega c hcycle huGraph c.start_mem_support s(ur, vr)
        ((SimpleGraph.mem_edgeSet _).2 hurv)
  have hulvCycle : s(ul, vl) ∈ c.edges :=
    rlc_twoChannelFullPhysical_contactCycle_covers
      gamma gamma' omega c hcycle huGraph c.start_mem_support s(ul, vl)
        ((SimpleGraph.mem_edgeSet _).2 hulv)
  have hurC : ur ∈ c.support :=
    c.fst_mem_support_of_mem_edges hurvCycle
  have hvrC : vr ∈ c.support :=
    c.snd_mem_support_of_mem_edges hurvCycle
  have hulC : ul ∈ c.support :=
    c.fst_mem_support_of_mem_edges hulvCycle
  have hvlC : vl ∈ c.support :=
    c.snd_mem_support_of_mem_edges hulvCycle
  rcases hTprov v hvT with rfl | rfl | rfl | rfl | ⟨r, hrReach, hrv⟩
  · exact False.elim (hvOff hvrC)
  · exact False.elim (hvOff hurC)
  · exact False.elim (hvOff hulC)
  · exact False.elim (hvOff hvlC)
  · rcases
        rlc_twoChannelFullPhysical_shiftedReach_inside_or_shortBoundaryContact
          c hcycle hrReach (by simpa [hrv] using hvOff) with
      hrInside | hrContact
    · exact Or.inl (by simpa [hrv] using hrInside)
    · exact Or.inr ⟨r, hrReach, hrv, hrContact⟩


theorem
    rlc_twoChannelFullPhysical_sourceSplice_contactInterval_firstVertex
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u ur vr ul vl s t : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (T : (hypercubicLattice 2).Walk s t)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift r = v)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    {i j : Nat} (hfirst : i + 1 < j) (hjLength : j ≤ T.length)
    (hbetween : ∀ l : Nat, i < l → l < j →
      T.getVert l ∉ c.support) :
    T.getVert (i + 1) ∈
        jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∨
      ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
        phb_doubleDualShift r = T.getVert (i + 1) ∧
          (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) := by
  apply
    rlc_twoChannelFullPhysical_sourceSplice_offContour_inside_or_tetherContact
      c hcycle T hTprov hurv hulv
  · exact T.getVert_mem_support (i + 1)
  · exact hbetween (i + 1) (by omega) hfirst


theorem
    rlc_twoChannelFullPhysical_sourceSplice_contactInterval_exterior_forces_tetherContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u ur vr ul vl s t : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (T : (hypercubicLattice 2).Walk s t)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift r = v)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    {i j : Nat} (hfirst : i + 1 < j) (hjLength : j ≤ T.length)
    (hbetween : ∀ l : Nat, i < l → l < j →
      T.getVert l ∉ c.support)
    (hfirstOutside : T.getVert (i + 1) ∉
      jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) :
    ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
      phb_doubleDualShift r = T.getVert (i + 1) ∧
        (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) := by
  rcases
      rlc_twoChannelFullPhysical_sourceSplice_contactInterval_firstVertex
        c hcycle T hTprov hurv hulv hfirst hjLength hbetween with
    hinside | hcontact
  · exact False.elim (hfirstOutside hinside)
  · exact hcontact


theorem rlc_walk_getVert_edge_mem
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (W : G.Walk a b) {i : Nat} (hi : i < W.length) :
    s(W.getVert i, W.getVert (i + 1)) ∈ W.edges := by
  rw [SimpleGraph.Walk.edges, List.mem_map]
  have hi' : i < W.darts.length := by simpa using hi
  refine ⟨W.darts[i], List.getElem_mem hi', ?_⟩
  rw [SimpleGraph.Walk.darts_getElem_eq_getVert i hi']
  rfl


theorem
    rlc_twoChannelFullPhysical_sourceSplice_contactInterval_adjacentEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b p p' ur vr ul vl s t : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (w : (hypercubicLattice 2).Walk p p')
    (T : (hypercubicLattice 2).Walk s t)
    (hTedge : ∀ e ∈ T.edges,
      (∀ z ∈ e, z = vr ∨ z = ur ∨
        z = phb_doubleDualShift p) ∨
      (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e) ∨
      ∀ z ∈ e, z = vl ∨ z = ul ∨
        z = phb_doubleDualShift p')
    {i j : Nat} (hij : j = i + 1) (hjLength : j ≤ T.length)
    (hiArc : T.getVert i ∈ (rlc_orderedContourArc c ha hb).support)
    (hjArc : T.getVert j ∈
      (rlc_complementaryContourArc c ha hb).support) :
    let e := s(T.getVert i, T.getVert j)
    (∀ z ∈ e, z = vr ∨ z = ur ∨
        z = phb_doubleDualShift p) ∨
      (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e ∧
        ∀ z ∈ Sym2.map phb_doubleDualShift e₀, z ∈ c.support) ∨
      ∀ z ∈ e, z = vl ∨ z = ul ∨
        z = phb_doubleDualShift p' := by
  dsimp only
  have hiLength : i < T.length := by omega
  have hedge : s(T.getVert i, T.getVert j) ∈ T.edges := by
    simpa [hij] using rlc_walk_getVert_edge_mem T hiLength
  have hedgeContact : ∀ z ∈ s(T.getVert i, T.getVert j),
      z ∈ c.support := by
    intro z hz
    rw [Sym2.mem_iff] at hz
    rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact rlc_orderedContourArc_support_subset c ha hb hiArc
    · exact rlc_complementaryContourArc_support_subset c ha hb hjArc
  rcases hTedge _ hedge with hright | ⟨e₀, he₀, heq⟩ | hleft
  · exact Or.inl hright
  · exact Or.inr (Or.inl ⟨e₀, he₀, heq, by
      intro z hz
      apply hedgeContact z
      rwa [← heq]⟩)
  · exact Or.inr (Or.inr hleft)


theorem rlc_twoChannelFullPhysical_shiftedExterior_shortBoundaryContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (haOutside : a ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))
    (hshiftInside : phb_doubleDualShift a ∈
      jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))
    (hshiftOffCycle : phb_doubleDualShift a ∉ c.support) :
    a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support := by
  let C := c.mapLe (faceBoundaryGraph_le
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
  let L := sw_lshape (a 0) (a 1) (a 0 - 1) (a 1 - 1)
  have hstart : (![a 0, a 1] : Site 2) = a := by
    ext i
    fin_cases i <;> simp
  have hend : (![a 0 - 1, a 1 - 1] : Site 2) =
      phb_doubleDualShift a := by
    ext i
    fin_cases i <;> simp [phb_doubleDualShift]
  have hopposite : rlc_OppositeLoopSides C
      (![a 0, a 1] : Site 2) ![a 0 - 1, a 1 - 1] := by
    left
    constructor
    · simpa [hstart, C, jec_mem_leftRegion] using haOutside
    · simpa [hend, jec_mem_leftRegion] using hshiftInside
  obtain ⟨z, hzL, hzC⟩ :=
    rlc_closedLoop_contact_of_opposite_sides C L hopposite
  have hzCycle : z ∈ c.support := by
    simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hzC
  dsimp only [L] at hzL
  rw [sw_lshape_mem_support] at hzL
  rcases hzL with hzHoriz | hzVert
  · rw [sw_horizSeg_mem_support] at hzHoriz
    obtain ⟨t, ht, rfl⟩ := hzHoriz
    rw [Set.mem_uIcc] at ht
    rcases ht with ht | ht
    · by_cases hta : t = a 0
      · left
        have heq : (![t, a 1] : Site 2) = a := by
          ext i
          fin_cases i <;> simp [hta]
        simpa [heq] using hzCycle
      · right
        have hta' : t = a 0 - 1 := by omega
        simpa [hta'] using hzCycle
    · by_cases hta : t = a 0
      · left
        have heq : (![t, a 1] : Site 2) = a := by
          ext i
          fin_cases i <;> simp [hta]
        simpa [heq] using hzCycle
      · right
        have hta' : t = a 0 - 1 := by omega
        simpa [hta'] using hzCycle
  · rw [sw_vertSeg_mem_support] at hzVert
    obtain ⟨t, ht, rfl⟩ := hzVert
    rw [Set.mem_uIcc] at ht
    rcases ht with ht | ht
    · by_cases hta : t = a 1
      · right
        simpa [hta] using hzCycle
      · have hta' : t = a 1 - 1 := by omega
        exact False.elim (hshiftOffCycle (by simpa [hend, hta'] using hzCycle))
    · by_cases hta : t = a 1
      · right
        simpa [hta] using hzCycle
      · have hta' : t = a 1 - 1 := by omega
        exact False.elim (hshiftOffCycle (by simpa [hend, hta'] using hzCycle))


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_separatorSourceSplice
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y z ur vr ul vl : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (htrace : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk
      gamma gamma' (z := z) (x := x) (y := y) flipLeft)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hdecR : rlc_orderedContourArc c hx hy =
      (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hurv rr))
    (hdecL : (rlc_complementaryContourArc c hx hy).reverse =
      (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hulv rl)) :
    ∃ (r s : Site 2)
      (hr : r ∈ rlc_pathVertices gamma.1)
      (hs : s ∈ rlc_pathVertices gamma.1)
      (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
      (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
      (p q p' q' : Site 2)
      (T : (hypercubicLattice 2).Walk vr vl)
      (V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)))
      (i j : Nat)
      (H : (hypercubicLattice 2).Walk
        ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i)
        ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j))
      (hi : (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert i ∈ c.support)
      (hj : (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert j ∈ c.support),
      rlc_dualReflect.symm r = x ∧
        rlc_dualReflect.symm (rlc_flipX s) = y ∧
        sharedPrimalEdge ur vr = s(p, q) ∧
        sharedPrimalEdge ul vl = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        (phb_doubleDualShift p ∈ s(ur, vr) ∨
          phb_doubleDualShift q ∈ s(ur, vr)) ∧
        (phb_doubleDualShift p' ∈ s(ul, vl) ∨
          phb_doubleDualShift q' ∈ s(ul, vl)) ∧
        (∀ v ∈ T.support,
          v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
            ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
              phb_doubleDualShift a = v) ∧
        (∃ v ∈ T.support, v 0 = -1 ∧
          (v = vr ∨ v = vl ∨
            ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
              a 0 = 0 ∧ phb_doubleDualShift a = v)) ∧
        (∃ (v : Site 2) (k : Nat),
          k ≤ T.length ∧ T.getVert k = v ∧ v 0 = -1 ∧
            (v ∈ c.support ∨
              ∃ i' j' : Nat,
                i' < k ∧ k < j' ∧ j' ≤ T.length ∧
                  T.getVert i' ∈ c.support ∧
                  T.getVert j' ∈ c.support ∧
                  ∀ l : Nat, i' < l → l < j' →
                    T.getVert l ∉ c.support)) ∧
        ((∃ v ∈ T.support,
            v ∈ (rlc_orderedContourArc c hx hy).support ∧
              v ∈ (rlc_complementaryContourArc c hx hy).support) ∨
          ∃ i' j' : Nat,
            i' < j' ∧ j' ≤ T.length ∧
              T.getVert i' ∈
                (rlc_orderedContourArc c hx hy).support ∧
              T.getVert j' ∈
                (rlc_complementaryContourArc c hx hy).support ∧
              ∀ l : Nat, i' < l → l < j' →
                T.getVert l ∉ c.support) ∧
        (H.append ((rlc_orderedContourArc c hi hj).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
        (H.append ((rlc_complementaryContourArc c hi hj).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧
        (((rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert i) 0 = -1 ∧
            ((rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert i) 1 < -1 ∨
          ((rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert i) 0 < -1) ∧
        rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i) ∈
            rlc_pathVertices gamma.1 ∧
        (rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j) ∈
            rlc_pathVertices gamma'.1 ∨
          (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j =
            rlc_dualReflect.symm
              (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) ∧
        ((((rlc_bookPhysicalTraceNetworkBracket
                gamma gamma' hr hs hsLeft hrs).getVert j) 0 = -1 ∧
              0 ≤ ((rlc_bookPhysicalTraceNetworkBracket
                gamma gamma' hr hs hsLeft hrs).getVert j) 1 ∨
            0 ≤ ((rlc_bookPhysicalTraceNetworkBracket
                gamma gamma' hr hs hsLeft hrs).getVert j) 0) ∨
          (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j =
            rlc_dualReflect.symm
              (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) ∧
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) ∈
          H.support ∧
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) ∉
          c.support ∧
        (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) ∉
          V.support ∧
        H.support ⊆ (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).support ∧
        (∀ v ∈ H.support,
          v = (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert i ∨
          v = (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j ∨
          (v ∉ c.support ∧
            v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
              (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧
        (∀ v ∈ V.support,
          v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧
        qr.support ⊆ V.support ∧ ql.support ⊆ V.support ∧
        T.support ⊆ V.support ∧
        (∀ v ∈ H.support, v ∈ V.support →
          v = (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert i ∨
            v = (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j ∨
            ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
              phb_doubleDualShift a = v ∧
                (a ∈ c.support ∨
                  (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧
                ((∃ w ∈ rlc_pathVertices gamma.1,
                    a = rlc_flipX w) ∨
                  ∃ w ∈ rlc_pathVertices gamma'.1,
                    a = rlc_flipX w)) ∧
        (∀ v ∈ V.support,
          v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil
            (rlc_dualReflect x)
            ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
              gamma.1 (rlc_dualReflect x)).2 hxPath)).map
                rlc_dualReflectSymmLatticeHom).support ∨
          v ∈ qr.support ∨ v = ur ∨ v = vr ∨ v ∈ T.support ∨
          v = vl ∨ v = ul ∨ v ∈ ql.support ∨
          v ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil
            (rlc_dualReflect y)
            ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
              gamma'.1 (rlc_dualReflect y)).2 hyPath)).map
                rlc_dualReflectSymmLatticeHom).support) ∧
        ∀ e ∈ V.edges,
          e ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil
            (rlc_dualReflect x)
            ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
              gamma.1 (rlc_dualReflect x)).2 hxPath)).map
                rlc_dualReflectSymmLatticeHom).edges ∨
          e ∈ qr.edges ∨ e = s(ur, vr) ∨ e ∈ T.edges ∨
          e = s(ul, vl) ∨ e ∈ ql.edges ∨
          e ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil
            (rlc_dualReflect y)
            ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
              gamma'.1 (rlc_dualReflect y)).2 hyPath)).map
                rlc_dualReflectSymmLatticeHom).edges := by
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
  have hurC : ur ∈ c.support := c.fst_mem_support_of_mem_edges
    (rlc_orderedContourArc_edges_subset c hx hy hurvArc)
  have hvrC : vr ∈ c.support := c.snd_mem_support_of_mem_edges
    (rlc_orderedContourArc_edges_subset c hx hy hurvArc)
  have hulC : ul ∈ c.support := c.fst_mem_support_of_mem_edges
    (rlc_complementaryContourArc_edges_subset c hx hy hulvArc)
  have hvlC : vl ∈ c.support := c.snd_mem_support_of_mem_edges
    (rlc_complementaryContourArc_edges_subset c hx hy hulvArc)
  obtain ⟨p, q, p', q', T, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOut, hqOut', hTprov, hTaxis⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_axisSourceSplice
      hrow hurv hulv
  have hincR := rlc_doubleDualShift_endpoint_mem_boundaryEdge
    hurv.1 hpqAdj hpq
  have hincL := rlc_doubleDualShift_endpoint_mem_boundaryEdge
    hulv.1 hpqAdj' hpq'
  have hTBox : ∀ v ∈ T.support,
      v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    intro v hv
    rcases hTprov v hv with rfl | rfl | rfl | rfl |
        ⟨a, haReach, rfl⟩
    · have hbox := rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
        hn gamma gamma' omega hurv.mem_support_right
      rw [mem_rect] at hbox ⊢
      omega
    · have hbox := rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
        hn gamma gamma' omega hurv.mem_support_left
      rw [mem_rect] at hbox ⊢
      omega
    · have hbox := rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
        hn gamma gamma' omega hulv.mem_support_left
      rw [mem_rect] at hbox ⊢
      omega
    · have hbox := rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
        hn gamma gamma' omega hulv.mem_support_right
      rw [mem_rect] at hbox ⊢
      omega
    · have hbox := rlc_doubleDualShift_mem_translatedRect
        (rlc_twoChannelFullReachSet_subset_box gamma gamma' omega haReach)
      rw [mem_rect] at hbox ⊢
      omega
  have hTtrim :
      (∃ v ∈ T.support,
        v ∈ (rlc_orderedContourArc c hx hy).support ∧
          v ∈ (rlc_complementaryContourArc c hx hy).support) ∨
        ∃ i' j' : Nat,
          i' < j' ∧ j' ≤ T.length ∧
            T.getVert i' ∈
              (rlc_orderedContourArc c hx hy).support ∧
            T.getVert j' ∈
              (rlc_complementaryContourArc c hx hy).support ∧
            ∀ l : Nat, i' < l → l < j' →
              T.getVert l ∉ c.support := by
    exact rlc_walk_ordered_to_complementary_contact_interval c hx hy T
      ((rlc_orderedContourArc c hx hy).snd_mem_support_of_mem_edges hurvArc)
      ((rlc_complementaryContourArc c hx hy).snd_mem_support_of_mem_edges
        hulvArc)
  have hTaxisTrim :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_axisContactInterval
      c hvrC hvlC hrow hurv.1 hulv.1 T hTprov
  obtain ⟨V, hVBox, hpreV, hpostV, hqrV, hqlV, hTV, hVprov,
      _hVedge⟩ :=
    rlc_twoChannelFullPhysical_innerTraceSourceSpliceWalk
      hfaith qr ql T hurv hulv hxPath hyPath hTBox
  obtain ⟨r, s, hr, hs, hsLeft, hrs, _Q, hrx, hsy,
      _hQSupport, _hQBox⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_canonicalPhysicalTraceNetworkBracket
      hyPath htrace
  subst x
  subst y
  obtain ⟨i, j, j', H, hi, hj, _hHPath, _hik, _hkj, _hjj',
      _hj'Length, _hj', _hiRight, _hj'Left, _hij'Ne, hdH, hdOff,
      hHB, hHclean, _hcycleOrdered, _hcycleComplementary, _hjCase⟩ :=
    rlc_bookPhysicalTraceNetworkBracket_exteriorChord_separatorCycles
      hn gamma gamma' hfaith omega hr hs hsLeft hrs c hcycle
        hx hy
  have hiPlace := hfaith.dualFace_rightContact_position _hiRight
  have hjProvenance :
      rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j) ∈
          rlc_pathVertices gamma'.1 ∨
        (rlc_bookPhysicalTraceNetworkBracket
            gamma gamma' hr hs hsLeft hrs).getVert j =
          rlc_dualReflect.symm
            (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
    rcases _hjCase with hjEq | ⟨hjCollar, _hjj', _hbetween⟩
    · left
      simpa [hjEq] using _hj'Left
    · exact Or.inr hjCollar
  have hjPlace :
      ((((rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j) 0 = -1 ∧
            0 ≤ ((rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j) 1) ∨
          0 ≤ ((rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j) 0) ∨
        (rlc_bookPhysicalTraceNetworkBracket
            gamma gamma' hr hs hsLeft hrs).getVert j =
          rlc_dualReflect.symm
            (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
    rcases _hjCase with hjEq | ⟨hjCollar, _hjj', _hbetween⟩
    · left
      apply hfaith.dualFace_leftContact_position
      simpa [hjEq] using _hj'Left
    · exact Or.inr hjCollar
  have hqrC {v : Site 2} (hv : v ∈ qr.support) : v ∈ c.support := by
    apply rlc_orderedContourArc_support_subset c hx hy
    rw [hdecR, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hv)
  have hqlC {v : Site 2} (hv : v ∈ ql.support) : v ∈ c.support := by
    apply rlc_complementaryContourArc_support_subset c hx hy
    have hvRev : v ∈
        (rlc_complementaryContourArc c hx hy).reverse.support := by
      rw [hdecL, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hv)
    simpa [SimpleGraph.Walk.support_reverse] using hvRev
  have hHV : ∀ v ∈ H.support, v ∈ V.support →
      v = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i ∨
        v = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift a = v ∧
            (a ∈ c.support ∨
              (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧
            ((∃ w ∈ rlc_pathVertices gamma.1,
                a = rlc_flipX w) ∨
              ∃ w ∈ rlc_pathVertices gamma'.1,
                a = rlc_flipX w) := by
    intro v hvH hvV
    rcases hHclean v hvH with hvi | hvj | hvOff
    · exact Or.inl hvi
    · exact Or.inr (Or.inl hvj)
    · rcases hVprov v hvV with hvPre | hvQr | rfl | rfl | hvT |
          rfl | rfl | hvQl | hvPost
      · have hvx :=
          rlc_bookPhysicalTraceNetworkBracket_meets_rightPrefix_only_start
            hfaith hr hs hsLeft hrs (hHB hvH) (by
              rw [SimpleGraph.Walk.support_map, List.mem_map] at hvPre ⊢
              obtain ⟨a, ha, hav⟩ := hvPre
              refine ⟨a, ?_, hav⟩
              rw [SimpleGraph.Walk.takeUntil_eq_take,
                SimpleGraph.Walk.support_copy] at ha ⊢
              have hrr : rlc_dualReflect (rlc_dualReflect.symm r) = r :=
                rlc_dualReflect.apply_symm_apply r
              rw [hrr] at ha
              exact ha)
        exact False.elim (hvOff.1 (hvx ▸ hx))
      · exact False.elim (hvOff.1 (hqrC hvQr))
      · exact False.elim (hvOff.1 hurC)
      · exact False.elim (hvOff.1 hvrC)
      · rcases hTprov v hvT with rfl | rfl | rfl | rfl | hvReach
        · exact False.elim (hvOff.1 hvrC)
        · exact False.elim (hvOff.1 hurC)
        · exact False.elim (hvOff.1 hulC)
        · exact False.elim (hvOff.1 hvlC)
        · obtain ⟨a, haReach, hav⟩ := hvReach
          have haOutside : phb_doubleDualShift a ∉
              jec_leftRegion (c.mapLe (faceBoundaryGraph_le
                (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
            simpa [hav] using hvOff.2
          refine Or.inr (Or.inr ?_)
          exact ⟨a, haReach, hav,
            rlc_twoChannelFullPhysical_shiftedReach_shortBoundaryContact
              c hcycle haReach haOutside (by simpa [hav] using hvOff.1),
            rlc_twoChannelFullPhysical_shiftedReach_bracket_cases
              hn hr hs hsLeft hrs haReach
                (by simpa [hav] using hHB hvH)⟩
      · exact False.elim (hvOff.1 hvlC)
      · exact False.elim (hvOff.1 hulC)
      · exact False.elim (hvOff.1 (hqlC hvQl))
      · have hvy :=
          rlc_bookPhysicalTraceNetworkBracket_meets_leftSuffix_only_end
            hfaith hr hs hsLeft hrs (hHB hvH) (by
              rw [SimpleGraph.Walk.support_map, List.mem_map] at hvPost ⊢
              obtain ⟨a, ha, hav⟩ := hvPost
              refine ⟨a, ?_, hav⟩
              rw [SimpleGraph.Walk.dropUntil_eq_drop,
                SimpleGraph.Walk.support_copy] at ha ⊢
              have hss : rlc_dualReflect
                  (rlc_dualReflect.symm (rlc_flipX s)) = rlc_flipX s :=
                rlc_dualReflect.apply_symm_apply (rlc_flipX s)
              rw [hss] at ha
              exact ha)
        exact False.elim (hvOff.1 (hvy ▸ hy))
  have hdV : rlc_dualReflect.symm
      (![(2 * n + 2), n + 2] : Site 2) ∉ V.support := by
    intro hdV
    rcases hHV _ hdH hdV with hdi | hdj |
        ⟨a, haReach, had, _haContact, _haTrace⟩
    · exact hdOff (hdi ▸ hi)
    · exact hdOff (hdj ▸ hj)
    · have haEq : a = rlc_flipX (![(2 * n + 2), n + 2] : Site 2) :=
        (rlc_doubleDualShift_eq_dualReflect_symm_iff a
          (![(2 * n + 2), n + 2] : Site 2)).1 had
      have haBox := rlc_twoChannelFullReachSet_subset_box
        gamma gamma' omega haReach
      rw [mem_rect] at haBox
      simp [haEq, rlc_flipX, rlc_flipXFun] at haBox
  exact ⟨r, s, hr, hs, hsLeft, hrs, p, q, p', q', T, V, i, j, H,
    hi, hj, rfl, rfl, hpq, hpq', hpqAdj, hpqAdj', hpReach, hpReach',
    hqOut, hqOut', hincR, hincL, hTprov, hTaxis, hTaxisTrim, hTtrim,
    _hcycleOrdered,
    _hcycleComplementary, hiPlace, _hiRight, hjProvenance, hjPlace,
    hdH, hdOff, hdV, hHB, hHclean,
    hVBox, hqrV, hqlV, hTV, hHV, hVprov, _hVedge⟩


theorem
    rlc_twoChannelFullPhysical_rowTwo_HVContact_axisFree_classification
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hrAxis : r ≠ (gamma.1.1 : Site 2))
    {u : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {i j : Nat}
    {H : (hypercubicLattice 2).Walk
      ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert i)
      ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert j)}
    {aV bV : Site 2} {V : (hypercubicLattice 2).Walk aV bV}
    (hHB : H.support ⊆ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support)
    (hHV : ∀ v ∈ H.support, v ∈ V.support →
      v = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i ∨
        v = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift a = v ∧
            (a ∈ c.support ∨
              (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧
            ((∃ w ∈ rlc_pathVertices gamma.1,
                a = rlc_flipX w) ∨
              ∃ w ∈ rlc_pathVertices gamma'.1,
                a = rlc_flipX w))
    {v : Site 2} (hvH : v ∈ H.support) (hvV : v ∈ V.support) :
    v = (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert i ∨
      v = (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert j ∨
      ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
        phb_doubleDualShift a = v ∧
          (a ∈ c.support ∨
            (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧
          (RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
              gamma gamma' a ∨
            ∃ w ∈ rlc_pathVertices gamma'.1,
              a = rlc_flipX w) := by
  rcases hHV v hvH hvV with hvi | hvj |
      ⟨a, haReach, hav, haContact, haRight | haLeft⟩
  · exact Or.inl hvi
  · exact Or.inr (Or.inl hvj)
  · obtain ⟨w, hwRight, haw⟩ := haRight
    rcases
        rlc_twoChannelFullPhysical_reachable_reflectedRight_axis_or_exclusive
          hfaith hno haReach hwRight haw with haAxis | haExclusive
    · subst a
      have hshiftH : phb_doubleDualShift (gamma.1.1 : Site 2) ∈
          H.support := by
        rw [← haAxis, hav]
        exact hvH
      exact False.elim
        ((rlc_bookPhysicalTraceNetworkBracket_axisSource_not_mem
          hfaith hr hs hsLeft hrs hrAxis) (hHB hshiftH))
    · exact Or.inr (Or.inr
        ⟨a, haReach, hav, haContact, Or.inl haExclusive⟩)
  · exact Or.inr (Or.inr
      ⟨a, haReach, hav, haContact, Or.inr haLeft⟩)


theorem
    rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_ne_chordEndpoints
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur ul : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    {r s : Site 2}
    {hr : r ∈ rlc_pathVertices gamma.1}
    {hs : s ∈ rlc_pathVertices gamma.1}
    {hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1}
    {hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s}
    {i j : Nat}
    (hiRight : rlc_dualReflect
        ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i) ∈
      rlc_pathVertices gamma.1)
    (hjProvenance :
      rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j) ∈
          rlc_pathVertices gamma'.1 ∨
        (rlc_bookPhysicalTraceNetworkBracket
            gamma gamma' hr hs hsLeft hrs).getVert j =
          rlc_dualReflect.symm
            (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) :
    ur ≠ (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i ∧
      ur ≠ (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j := by
  constructor
  · intro hur
    exact hrow.2.1.2.2.1 (hur ▸ hiRight)
  · intro hur
    rcases hjProvenance with hjLeft | hjCollar
    · exact hrow.2.1.2.2.2 (hur ▸ hjLeft)
    · have hcoord := congrArg (fun z : Site 2 => z 0)
          (congrArg rlc_dualReflect (hur.trans hjCollar))
      have hpositive := hrow.2.1.1
      simp only [rlc_dualReflect.apply_symm_apply,
        Matrix.cons_val_zero] at hcoord
      omega


theorem
    rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_sourceWitness_of_HV
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur ul : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    {r s : Site 2}
    {hr : r ∈ rlc_pathVertices gamma.1}
    {hs : s ∈ rlc_pathVertices gamma.1}
    {hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1}
    {hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s}
    {i j : Nat}
    (hiRight : rlc_dualReflect
        ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i) ∈
      rlc_pathVertices gamma.1)
    (hjProvenance :
      rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j) ∈
          rlc_pathVertices gamma'.1 ∨
        (rlc_bookPhysicalTraceNetworkBracket
            gamma gamma' hr hs hsLeft hrs).getVert j =
          rlc_dualReflect.symm
            (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2))
    (hclass :
      ur = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i ∨
        ur = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift a = ur ∧
            (RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                gamma gamma' a ∨
              ∃ w ∈ rlc_pathVertices gamma'.1,
                a = rlc_flipX w)) :
    ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
      phb_doubleDualShift a = ur ∧
        (RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
            gamma gamma' a ∨
          ∃ w ∈ rlc_pathVertices gamma'.1,
            a = rlc_flipX w) := by
  obtain ⟨hurI, hurJ⟩ :=
    rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_ne_chordEndpoints
      hn hrow hiRight hjProvenance
  rcases hclass with huri | hurj | hsource
  · exact False.elim (hurI huri)
  · exact False.elim (hurJ hurj)
  · exact hsource


theorem
    rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_HV_sourceWitness
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur ul : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
    (hrAxis : r ≠ (gamma.1.1 : Site 2))
    {u : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {i j : Nat}
    {H : (hypercubicLattice 2).Walk
      ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert i)
      ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert j)}
    {aV bV : Site 2} {V : (hypercubicLattice 2).Walk aV bV}
    (hHB : H.support ⊆ (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).support)
    (hHV : ∀ v ∈ H.support, v ∈ V.support →
      v = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i ∨
        v = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift a = v ∧
            (a ∈ c.support ∨
              (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧
            ((∃ w ∈ rlc_pathVertices gamma.1,
                a = rlc_flipX w) ∨
              ∃ w ∈ rlc_pathVertices gamma'.1,
                a = rlc_flipX w))
    (hiRight : rlc_dualReflect
        ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i) ∈
      rlc_pathVertices gamma.1)
    (hjProvenance :
      rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j) ∈
          rlc_pathVertices gamma'.1 ∨
        (rlc_bookPhysicalTraceNetworkBracket
            gamma gamma' hr hs hsLeft hrs).getVert j =
          rlc_dualReflect.symm
            (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2))
    (hurH : ur ∈ H.support) (hurV : ur ∈ V.support) :
    ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
      phb_doubleDualShift a = ur ∧
        (a ∈ c.support ∨
          (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧
        (RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
            gamma gamma' a ∨
          ∃ w ∈ rlc_pathVertices gamma'.1,
            a = rlc_flipX w) := by
  have hclass :=
    rlc_twoChannelFullPhysical_rowTwo_HVContact_axisFree_classification
      hfaith hno hr hs hsLeft hrs hrAxis hHB hHV hurH hurV
  obtain ⟨hurI, hurJ⟩ :=
    rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_ne_chordEndpoints
      hn hrow hiRight hjProvenance
  rcases hclass with huri | hurj | hsource
  · exact False.elim (hurI huri)
  · exact False.elim (hurJ hurj)
  · exact hsource


theorem rlc_twoChannelFullPhysical_Hclean_cycleContact_endpoints
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {r s : Site 2}
    {hr : r ∈ rlc_pathVertices gamma.1}
    {hs : s ∈ rlc_pathVertices gamma.1}
    {hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1}
    {hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s}
    {u v : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {i j : Nat}
    {H : (hypercubicLattice 2).Walk
      ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert i)
      ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert j)}
    (hclean : ∀ z ∈ H.support,
      z = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i ∨
        z = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j ∨
        (z ∉ c.support ∧
          z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (hvH : v ∈ H.support) (hvC : v ∈ c.support) :
    v = (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert i ∨
      v = (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert j := by
  rcases hclean v hvH with hvi | hvj | hvOff
  · exact Or.inl hvi
  · exact Or.inr hvj
  · exact False.elim (hvOff.1 hvC)


theorem
    rlc_twoChannelFullPhysical_Hclean_shiftedReflectedRight_eq_firstEndpoint
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {r s p v : Site 2}
    {hr : r ∈ rlc_pathVertices gamma.1}
    {hs : s ∈ rlc_pathVertices gamma.1}
    {hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1}
    {hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s}
    {u : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {i j : Nat}
    {H : (hypercubicLattice 2).Walk
      ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert i)
      ((rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert j)}
    (hclean : ∀ z ∈ H.support,
      z = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i ∨
        z = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j ∨
        (z ∉ c.support ∧
          z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (hvH : v ∈ H.support) (hvC : v ∈ c.support)
    (hshift : phb_doubleDualShift p = v)
    {w : Site 2} (hwRight : w ∈ rlc_pathVertices gamma.1)
    (hpw : p = rlc_flipX w)
    (hjProvenance :
      rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j) ∈
          rlc_pathVertices gamma'.1 ∨
        (rlc_bookPhysicalTraceNetworkBracket
            gamma gamma' hr hs hsLeft hrs).getVert j =
          rlc_dualReflect.symm
            (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) :
    v = (rlc_bookPhysicalTraceNetworkBracket
      gamma gamma' hr hs hsLeft hrs).getVert i := by
  rcases rlc_twoChannelFullPhysical_Hclean_cycleContact_endpoints
      hclean hvH hvC with hvi | hvj
  · exact hvi
  · exfalso
    have hvDual : rlc_dualReflect v = w := by
      rw [← hshift, hpw,
        rlc_doubleDualShift_flipX_eq_dualReflect_symm,
        rlc_dualReflect.apply_symm_apply]
    rcases hjProvenance with hjLeft | hjCollar
    · have hwLeft : w ∈ rlc_pathVertices gamma'.1 := by
        rw [← hvDual, hvj]
        exact hjLeft
      exact (Finset.disjoint_left.mp hfaith.exposed_disjoint)
        hwRight hwLeft
    · have hwBox := rlc_pathVertex_mem_rect gamma.1 hwRight
      have hcoord := congrArg (fun z : Site 2 => z 0)
        (hvDual.symm.trans (by
          rw [hvj, hjCollar, rlc_dualReflect.apply_symm_apply]))
      rw [mem_rect] at hwBox
      simp only [Matrix.cons_val_zero] at hcoord
      omega


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceEdge_separatorContact
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {u x y z ur vr ul vl : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (htrace : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk
      gamma gamma' (z := z) (x := x) (y := y) flipLeft)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hdecR : rlc_orderedContourArc c hx hy =
      (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hurv rr))
    (hdecL : (rlc_complementaryContourArc c hx hy).reverse =
      (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hulv rl)) :
    ∃ (r s : Site 2)
      (hr : r ∈ rlc_pathVertices gamma.1)
      (hs : s ∈ rlc_pathVertices gamma.1)
      (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
      (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
      (p q p' q' : Site 2)
      (V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)))
      (i j : Nat)
      (H : (hypercubicLattice 2).Walk
        ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i)
        ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j))
      (hi : (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert i ∈ c.support)
      (hj : (rlc_bookPhysicalTraceNetworkBracket
        gamma gamma' hr hs hsLeft hrs).getVert j ∈ c.support),
      sharedPrimalEdge ur vr = s(p, q) ∧
        sharedPrimalEdge ul vl = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i) ∈
            rlc_pathVertices gamma.1 ∧
        (rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j) ∈
            rlc_pathVertices gamma'.1 ∨
          (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j =
            rlc_dualReflect.symm
              (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) ∧
        H.support ⊆ (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).support ∧
        (∀ v ∈ H.support,
          v = (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert i ∨
            v = (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j ∨
            (v ∉ c.support ∧
              v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
                (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧
        (∀ v ∈ H.support, v ∈ V.support →
          v = (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert i ∨
            v = (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j ∨
            ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
              phb_doubleDualShift a = v ∧
                (a ∈ c.support ∨
                  (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧
                ((∃ w ∈ rlc_pathVertices gamma.1,
                    a = rlc_flipX w) ∨
                  ∃ w ∈ rlc_pathVertices gamma'.1,
                    a = rlc_flipX w)) ∧
        (p = vr → p ∈ V.support ∧ p ∈ c.support) ∧
        (∀ v ∈ V.support,
          v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil
            (rlc_dualReflect x)
            ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
              gamma.1 (rlc_dualReflect x)).2 hxPath)).map
                rlc_dualReflectSymmLatticeHom).support ∨
          v ∈ qr.support ∨ v = ur ∨ v = vr ∨
          (∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
            phb_doubleDualShift a = v) ∨
          v = vl ∨ v = ul ∨ v ∈ ql.support ∨
          v ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil
            (rlc_dualReflect y)
            ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
              gamma'.1 (rlc_dualReflect y)).2 hyPath)).map
                rlc_dualReflectSymmLatticeHom).support) ∧
        (p ∈ H.support →
          p = (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert i ∨
            p = (rlc_bookPhysicalTraceNetworkBracket
              gamma gamma' hr hs hsLeft hrs).getVert j) ∧
        (q = ur → q ∉ H.support) ∧
        (p ∈ c.support ∨ q ∈ c.support ∨
          (q ∈ H.support ∧
            ((p = ur ∧ phb_doubleDualShift q = vr ∧
                ∃ w ∈ rlc_pathVertices gamma'.1,
                  q = ![w 0 - 1, w 1] ∨ q = ![w 0, w 1 - 1]) ∨
              (p = vr ∧ phb_doubleDualShift q = ur ∧
                ∃ w ∈ rlc_pathVertices gamma'.1, q = w ∧
                  ((sharedPrimalEdge ur vr =
                      s((![w 0, w 1 - 1] : Site 2), w) ∧
                    s((![w 0, w 1 - 1] : Site 2), w) ∉
                      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∨
                   (sharedPrimalEdge ur vr =
                      s((![w 0 - 1, w 1] : Site 2), w) ∧
                    s((![w 0 - 1, w 1] : Site 2), w) ∉
                      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)))))) ∧
        ((p ∈ H.support ∨ q ∈ H.support ∨
            p ∈ (rlc_orderedContourArc c hi hj).support ∨
            q ∈ (rlc_orderedContourArc c hi hj).support) ∨
          (p ∈ H.support ∨ q ∈ H.support ∨
            p ∈ (rlc_complementaryContourArc c hi hj).support ∨
            q ∈ (rlc_complementaryContourArc c hi hj).support)) ∧
        ((phb_doubleDualShift p = vr ∧ q = ur) ∨
          (p = ur ∧ phb_doubleDualShift q = vr) ∨
          (p = vr ∧ phb_doubleDualShift q = ur)) ∧
        (RlcTwoChannelFullPhysicalSourceCarrierGeometry
            gamma gamma' ur vr ∨
          RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
            gamma gamma' p ∨
          (p 0 = -2 * n ∨ p 0 = 2 * n ∨
            p 1 = -n ∨ p 1 = n)) ∧
        (p = vr →
          RlcTwoChannelFullPhysicalSourceCarrierGeometry
              gamma gamma' ur vr ∨
            ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                gamma gamma' p ∨
              p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧
             sharedPrimalEdge ur vr ∉
                rlc_connectorFourTraceEdges gamma gamma')) ∧
        (p = vr →
          RlcTwoChannelFullPhysicalSourceCarrierGeometry
              gamma gamma' ur vr ∨
            (p ∈ c.support ∧
              ((p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∨
                ∃ z : Site 2,
                  RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                      gamma gamma' p ∧
                    sharedPrimalEdge ur vr ∉
                      rlc_connectorFourTraceEdges gamma gamma' ∧
                    (hypercubicLattice 2).Adj p z ∧
                    rlc_twoChannelFullAmbientConfig gamma gamma' omega
                        s(p, z) = true ∧
                    (s(p, z) ∈
                        rlc_connectorFourTraceEdges gamma gamma' ∨
                      (z 0 + q 0 = 2 * p 0 ∧
                        z 1 + q 1 = 2 * p 1))))) ∧
        (phb_doubleDualShift p = vr ∨ p = ur ∨ p = vr) ∧
        (phb_doubleDualShift p ∈ c.support ∨ p ∈ c.support) := by
  obtain ⟨r, s, hr, hs, hsLeft, hrs, p, q, p', q', T, V, i, j, H,
      hi, hj, _hrx, _hsy, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOut, hqOut', _hincR, _hincL, _hTprov, _hTaxis,
      _hTaxisTrim, _hTtrim, _hcycleOrdered, _hcycleComplementary,
      _hiPlace, hiRight, hjProvenance, _hjPlace, _hdH, _hdOff, _hdV,
      hHB, hHclean, _hVBox, hqrV, _hqlV, hTV, hHV, hVprov, _hVedge⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_separatorSourceSplice
      hn hfaith c hcycle hx hy hxPath hyPath htrace qr rr ql hrow rl
        hurv hulv hdecR hdecL
  have hcontact :=
    rlc_twoChannelFullPhysical_insideOutsideEdge_endpointContact_cases
      c hcycle hi hj H hpqAdj hpReach hqOut
  have hVprov' : ∀ v ∈ V.support,
      v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil
        (rlc_dualReflect x)
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma.1 (rlc_dualReflect x)).2 hxPath)).map
            rlc_dualReflectSymmLatticeHom).support ∨
      v ∈ qr.support ∨ v = ur ∨ v = vr ∨
      (∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
        phb_doubleDualShift a = v) ∨
      v = vl ∨ v = ul ∨ v ∈ ql.support ∨
      v ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil
        (rlc_dualReflect y)
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 (rlc_dualReflect y)).2 hyPath)).map
            rlc_dualReflectSymmLatticeHom).support := by
    intro v hv
    rcases hVprov v hv with hpre | hqr | hur | hvr | hT |
        hvl | hul | hql | hpost
    · exact Or.inl hpre
    · exact Or.inr (Or.inl hqr)
    · exact Or.inr (Or.inr (Or.inl hur))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hvr)))
    · rcases _hTprov v hT with hvr | hur | hul | hvl | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inl hvr)))
      · exact Or.inr (Or.inr (Or.inl hur))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hul))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl hul))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl hql)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr hpost)))))))
  have hpChordEndpoint (hpH : p ∈ H.support) :
      p = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert i ∨
        p = (rlc_bookPhysicalTraceNetworkBracket
          gamma gamma' hr hs hsLeft hrs).getVert j := by
    have hpInside : p ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
      rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
        gamma gamma' omega c hcycle]
      exact rlc_twoChannelFullReachSet_subset_filled
        gamma gamma' omega hpReach
    rcases hHclean p hpH with hpi | hpj | hpOutside
    · exact Or.inl hpi
    · exact Or.inr hpj
    · exact False.elim (hpOutside.2 hpInside)
  have hqUrNotH (hqUr : q = ur) : q ∉ H.support := by
    intro hqH
    have hurH : ur ∈ H.support := by simpa [hqUr] using hqH
    have hurV : ur ∈ V.support := hqrV qr.end_mem_support
    obtain ⟨hurI, hurJ⟩ :=
      rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_ne_chordEndpoints
        hn hrow hiRight hjProvenance
    rcases hHV ur hurH hurV with hurEqI | hurEqJ |
        ⟨a, haReach, haShift, _haContact, _haTrace⟩
    · exact hurI hurEqI
    · exact hurJ hurEqJ
    · exact (rlc_shiftedReach_ne_exclusiveReflectedLeftFace
        hno haReach hrow.2.1) haShift
  have hdropExact :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_exact_cases
      hno hrow hurv.1 hulv.1 hpq hpq' hpReach hqOut'
  have hdrop :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cases
      hno hrow hurv.1 hulv.1 hpq hpq' hpReach hqOut'
  have hsourceLocation :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceCarrier_or_location
      hno hrow hurv hulv.1 hpq hpq' hpqAdj hpReach hqOut'
  have hpVrNonwall (hpVr : p = vr) :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_nonwall_location
      hn hno hrow hurv hulv.1 hpq hpq' hpqAdj hpReach hqOut' hpVr
  have hpChordCycle (hpH : p ∈ H.support) : p ∈ c.support := by
    rcases hpChordEndpoint hpH with hpi | hpj
    · simpa [hpi] using hi
    · simpa [hpj] using hj
  have hcontactReduced : p ∈ c.support ∨ q ∈ c.support ∨
      (q ∈ H.support ∧
        ((p = ur ∧ phb_doubleDualShift q = vr ∧
            ∃ w ∈ rlc_pathVertices gamma'.1,
              q = ![w 0 - 1, w 1] ∨ q = ![w 0, w 1 - 1]) ∨
          (p = vr ∧ phb_doubleDualShift q = ur ∧
            ∃ w ∈ rlc_pathVertices gamma'.1, q = w ∧
              ((sharedPrimalEdge ur vr =
                  s((![w 0, w 1 - 1] : Site 2), w) ∧
                s((![w 0, w 1 - 1] : Site 2), w) ∉
                  rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∨
               (sharedPrimalEdge ur vr =
                  s((![w 0 - 1, w 1] : Site 2), w) ∧
                s((![w 0 - 1, w 1] : Site 2), w) ∉
                  rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1))))) := by
    rcases hcontact with (hpH | hqH | hpArc | hqArc) |
        (hpH | hqH | hpArc | hqArc)
    · exact Or.inl (hpChordCycle hpH)
    · rcases hdropExact with hshift | hpUr | hpVr
      · exact False.elim ((hqUrNotH hshift.2) hqH)
      · exact Or.inr (Or.inr ⟨hqH, Or.inl
          ⟨hpUr.1, hpUr.2,
            rlc_twoChannelFullPhysical_wallFamilyRowTwo_exteriorNeighbour_of_p_eq_ur
              hno hrow hurv.1 hulv.1 hpq hpq' hpReach hqOut' hpUr.1⟩⟩)
      · exact Or.inr (Or.inr ⟨hqH, Or.inr
          ⟨hpVr.1, hpVr.2,
            rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceEdge_traceGap
              hno hrow hurv hulv.1 hpq hpq' hpReach hqOut' hpVr.1⟩⟩)
    · exact Or.inl (rlc_orderedContourArc_support_subset c hi hj hpArc)
    · exact Or.inr (Or.inl
        (rlc_orderedContourArc_support_subset c hi hj hqArc))
    · exact Or.inl (hpChordCycle hpH)
    · rcases hdropExact with hshift | hpUr | hpVr
      · exact False.elim ((hqUrNotH hshift.2) hqH)
      · exact Or.inr (Or.inr ⟨hqH, Or.inl
          ⟨hpUr.1, hpUr.2,
            rlc_twoChannelFullPhysical_wallFamilyRowTwo_exteriorNeighbour_of_p_eq_ur
              hno hrow hurv.1 hulv.1 hpq hpq' hpReach hqOut' hpUr.1⟩⟩)
      · exact Or.inr (Or.inr ⟨hqH, Or.inr
          ⟨hpVr.1, hpVr.2,
            rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceEdge_traceGap
              hno hrow hurv hulv.1 hpq hpq' hpReach hqOut' hpVr.1⟩⟩)
    · exact Or.inl
        (rlc_complementaryContourArc_support_subset c hi hj hpArc)
    · exact Or.inr (Or.inl
        (rlc_complementaryContourArc_support_subset c hi hj hqArc))
  have hurvArc : s(ur, vr) ∈
      (rlc_orderedContourArc c hx hy).edges := by
    rw [hdecR, SimpleGraph.Walk.edges_append]
    simp
  have hurC : ur ∈ c.support := c.fst_mem_support_of_mem_edges
    (rlc_orderedContourArc_edges_subset c hx hy hurvArc)
  have hvrC : vr ∈ c.support := c.snd_mem_support_of_mem_edges
    (rlc_orderedContourArc_edges_subset c hx hy hurvArc)
  have hpVrOnSplice (hpVr : p = vr) : p ∈ V.support ∧ p ∈ c.support := by
    constructor
    · simpa [hpVr] using hTV T.start_mem_support
    · simpa [hpVr] using hvrC
  have hpVrSplice (hpVr : p = vr) :
      RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨
        (p ∈ c.support ∧
          ((p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∨
            ∃ z : Site 2,
              RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                  gamma gamma' p ∧
                sharedPrimalEdge ur vr ∉
                  rlc_connectorFourTraceEdges gamma gamma' ∧
                (hypercubicLattice 2).Adj p z ∧
                rlc_twoChannelFullAmbientConfig gamma gamma' omega
                    s(p, z) = true ∧
                (s(p, z) ∈ rlc_connectorFourTraceEdges gamma gamma' ∨
                  (z 0 + q 0 = 2 * p 0 ∧
                    z 1 + q 1 = 2 * p 1)))) := by
    have hpCycle : p ∈ c.support := by simpa [hpVr] using hvrC
    rcases
        rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourcePrefix_capstone
          hn hno hrow hurv hulv.1 hpq hpq' hpqAdj hpReach hqOut' hpVr with
      hsource | hpBoundary | ⟨z, hz⟩
    · exact Or.inl hsource
    · exact Or.inr ⟨hpCycle, Or.inl hpBoundary⟩
    · exact Or.inr ⟨hpCycle, Or.inr ⟨z, hz⟩⟩
  have hcycleContact :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cycleContact
      hno hrow hurv.1 hulv.1 hpq hpq' hpReach hqOut' c hurC hvrC
  exact ⟨r, s, hr, hs, hsLeft, hrs, p, q, p', q', V, i, j, H, hi, hj,
    hpq, hpq', hpqAdj, hpqAdj', hpReach, hpReach', hqOut, hqOut',
    hiRight, hjProvenance, hHB, hHclean, hHV, hpVrOnSplice, hVprov',
    hpChordEndpoint, hqUrNotH,
    hcontactReduced, hcontact, hdropExact, hsourceLocation, hpVrNonwall,
    hpVrSplice, hdrop, hcycleContact⟩


theorem rlc_bookOuterTraceNetworkArc_mem_rect {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {s v : Site 2}
    (hsRight : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hv : v ∈ (rlc_bookOuterTraceNetworkArc
      gamma gamma' hsRight hsLeft).support) :
    v ∈ rect (-2 * n - 2) (2 * n + 2) (-n) (n + 2) := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hsWR : s ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2
      hsRight
  have hsWL : rlc_flipX s ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft
  change v ∈ (((WR.dropUntil s hsWR).append
    (rlc_bookExteriorEndpointDetour gamma gamma')).append
      (WL.takeUntil (rlc_flipX s) hsWL)).support at hv
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with (hvRight | hvDetour) | hvLeft
  · have hvWR : v ∈ WR.support := WR.support_dropUntil_subset hsWR hvRight
    have hvPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 v).1
        hvWR
    have hvBox := rlc_pathVertex_mem_rect gamma.1 hvPath
    rw [mem_rect] at hvBox ⊢
    omega
  · exact rlc_bookExteriorEndpointDetour_mem_rect
      gamma gamma' hvDetour
  · have hvWL : v ∈ WL.support :=
      WL.support_takeUntil_subset_support hsWL hvLeft
    have hvPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 v).1
        hvWL
    have hvBox := rlc_pathVertex_mem_rect gamma'.1 hvPath
    rw [mem_rect] at hvBox ⊢
    omega


theorem rlc_bookPhysicalOuterTraceNetworkArc_mem_rect {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {s v : Site 2}
    (hsRight : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hv : v ∈ (rlc_bookPhysicalOuterTraceNetworkArc
      gamma gamma' hsRight hsLeft).support) :
    v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1) := by
  change v ∈ ((rlc_bookOuterTraceNetworkArc
    gamma gamma' hsRight hsLeft).map
      rlc_dualReflectSymmLatticeHom).support at hv
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  have hwBox := rlc_bookOuterTraceNetworkArc_mem_rect
    gamma gamma' hsRight hsLeft hw
  change rlc_dualReflect.symm w ∈
    rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1)
  rw [mem_rect] at hwBox ⊢
  simp only [rlc_dualReflect_symm_zero, rlc_dualReflect_symm_one]
  omega


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_physicalOuterTraceNetworkBracketWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    ∃ (r s : Site 2) (Q : (hypercubicLattice 2).Walk x y),
      r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' ∧
        ∃ (hsRight : s ∈ rlc_pathVertices gamma.1)
          (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1),
          rlc_dualReflect.symm z ∈ Q.support ∧
          (rlc_bookPhysicalOuterTraceNetworkArc
            gamma gamma' hsRight hsLeft).support ⊆ Q.support ∧
          ∀ v ∈ Q.support,
            v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1) := by
  obtain ⟨r, s, P, hrSet, hsPath, hsFlipLeft, hxr, hys,
    _hrz, _hzs, hzP, hP⟩ := h
  have hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1 := by
    rw [hys] at hyPath
    exact hyPath
  have hrx : rlc_dualReflect.symm r = x := by
    rw [← hxr]
    exact rlc_dualReflect.symm_apply_apply x
  have hsy : rlc_dualReflect.symm (rlc_flipX s) = y := by
    rw [← hys]
    exact rlc_dualReflect.symm_apply_apply y
  let mapped := P.map rlc_dualReflectSymmLatticeHom
  let outer := rlc_bookPhysicalOuterTraceNetworkArc
    gamma gamma' hsPath hsLeft
  let Q : (hypercubicLattice 2).Walk x y :=
    (mapped.append outer).copy hrx hsy
  refine ⟨r, s, Q, hrSet, hsPath, hsLeft, ?_, ?_, ?_⟩
  · dsimp only [Q]
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    dsimp only [mapped]
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨z, hzP, rfl⟩
  · intro v hvOuter
    dsimp only [Q]
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr (by simpa [outer] using hvOuter)
  · intro v hv
    dsimp only [Q] at hv
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hvMapped | hvOuter
    · dsimp only [mapped] at hvMapped
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hvMapped
      obtain ⟨w, hw, rfl⟩ := hvMapped
      have hwPath : w ∈ rlc_pathVertices gamma.1 :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 w).1
          (hP w hw)
      have hwBox := rlc_pathVertex_mem_rect gamma.1 hwPath
      change rlc_dualReflect.symm w ∈
        rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1)
      rw [mem_rect] at hwBox ⊢
      simp only [rlc_dualReflect_symm_zero, rlc_dualReflect_symm_one]
      omega
    · exact rlc_bookPhysicalOuterTraceNetworkArc_mem_rect
        gamma gamma' hsPath hsLeft hvOuter


theorem rlc_bookRowOne_flippedLeftEndpoint_mem {n : Int}
    (gamma' : RlcLeftDiagonalPath n) :
    rlc_flipX (rlc_flipX (gamma'.1.2.1 : Site 2)) ∈
      rlc_pathVertices gamma'.1 := by
  simpa using rlc_connector_path_end_mem_vertices gamma'.1


end
end StatMech.Universality
