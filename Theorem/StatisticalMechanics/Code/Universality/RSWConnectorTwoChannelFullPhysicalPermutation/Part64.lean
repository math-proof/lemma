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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part64
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_traceBracketWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceSegmentCases
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk
      gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
  have hzSet : z ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' :=
    (Finset.mem_filter.mp hzCandidate).1
  have hzPath : z ∈ rlc_pathVertices gamma.1 :=
    (Finset.mem_filter.mp hzSet).1
  rcases h with hEq | hEarlier | hLater | hBoth
  · refine ⟨z, z, .nil, hzSet, hzPath, flipLeft.start_mem_support,
      hEq.1, hEq.2, le_rfl, le_rfl, ?_, ?_⟩
    · exact SimpleGraph.Walk.start_mem_support _
    · intro v hv
      have hvz : v = z := by simpa using hv
      subst v
      exact
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2
          hzPath
  · obtain ⟨r, q, P, hrSet, hxr, hrz, hqCandidate, hqr, hqz, hP⟩ :=
      hEarlier.1
    refine ⟨r, z, P, hrSet, hzPath, flipLeft.start_mem_support,
      hxr, hEarlier.2, hrz, le_rfl, P.end_mem_support, hP⟩
  · obtain ⟨s, P, hsPath, hys, hsSupport, hzs, hP⟩ := hLater.2
    refine ⟨z, s, P, hzSet, hsPath, hsSupport, hLater.1, hys, le_rfl,
      Nat.le_of_lt hzs,
      P.start_mem_support, hP⟩
  · obtain ⟨r, q, P, hrSet, hxr, hrz, hqCandidate, hqr, hqz, hP⟩ :=
      hBoth.1
    obtain ⟨s, Q, hsPath, hys, hsSupport, hzs, hQ⟩ := hBoth.2
    refine ⟨r, s, P.append Q, hrSet, hsPath, hsSupport, hxr, hys,
      hrz, Nat.le_of_lt hzs, ?_, ?_⟩
    · rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl P.end_mem_support
    · intro v hv
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv
      exact hv.elim (hP v) (hQ v)


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_physicalTraceBracketWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    ∃ Q : (hypercubicLattice 2).Walk x y,
      rlc_dualReflect.symm z ∈ Q.support ∧
        ∀ v ∈ Q.support,
          v ∈ rect (-2 * n - 4) (2 * n + 2) (-n - 4) (n + 2) := by
  obtain ⟨r, s, P, hrSet, hsPath, hsSuffix, hxr, hys,
    _hrz, _hzs, hzP, hP⟩ := h
  have hrx : rlc_dualReflect.symm r = x := by
    rw [← hxr]
    exact rlc_dualReflect.symm_apply_apply x
  have hsy : rlc_dualReflect.symm (rlc_flipX s) = y := by
    rw [← hys]
    exact rlc_dualReflect.symm_apply_apply y
  let mapped := P.map rlc_dualReflectSymmLatticeHom
  have hbridgeStart : (![(-s 0 - 1), s 1 - 1] : Site 2) =
      rlc_dualReflect.symm s := by
    ext i
    fin_cases i <;> simp
  have hbridgeEnd : (![(s 0 - 1), s 1 - 1] : Site 2) =
      rlc_dualReflect.symm (rlc_flipX s) := by
    ext i
    fin_cases i <;> simp [rlc_flipX, rlc_flipXFun]
  let bridge : (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm s)
      (rlc_dualReflect.symm (rlc_flipX s)) :=
    (sw_horizSeg (s 1 - 1) (-s 0 - 1) (s 0 - 1)).copy
      hbridgeStart hbridgeEnd
  have hbridgeSupport : bridge.support =
      (sw_horizSeg (s 1 - 1) (-s 0 - 1) (s 0 - 1)).support := by
    dsimp only [bridge]
    exact SimpleGraph.Walk.support_copy _ _ _
  let Q : (hypercubicLattice 2).Walk x y :=
    (mapped.append bridge).copy hrx hsy
  have hsBox : s ∈ rect 0 (2 * n) (-n) n :=
    rlc_pathVertex_mem_rect gamma.1 hsPath
  have hzMapped : rlc_dualReflect.symm z ∈ mapped.support := by
    dsimp only [mapped]
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨z, hzP, rfl⟩
  refine ⟨Q, ?_, ?_⟩
  · dsimp only [Q]
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hzMapped
  · intro v hv
    dsimp only [Q] at hv
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hvMapped | hvBridge
    · dsimp only [mapped] at hvMapped
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hvMapped
      obtain ⟨w, hwP, rfl⟩ := hvMapped
      have hwPath : w ∈ rlc_pathVertices gamma.1 :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 w).1
          (hP w hwP)
      have hwBox := rlc_pathVertex_mem_rect gamma.1 hwPath
      change rlc_dualReflect.symm w ∈
        rect (-2 * n - 4) (2 * n + 2) (-n - 4) (n + 2)
      rw [mem_rect] at hwBox ⊢
      simp [rlc_dualReflect, rlc_dualReflectInvFun]
      omega
    · have hvBase : v ∈
          (sw_horizSeg (s 1 - 1) (-s 0 - 1) (s 0 - 1)).support := by
        exact (congrArg (fun L : List (Site 2) => v ∈ L)
          hbridgeSupport).mp hvBridge
      rw [sw_horizSeg_mem_support] at hvBase
      obtain ⟨t, ht, rfl⟩ := hvBase
      rw [Set.mem_uIcc] at ht
      rw [mem_rect] at hsBox ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega


theorem rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
    {n : Int} (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {v : Site 2}
    (hv : v ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    v ∈ rect (-2 * n - 1) (2 * n) (-n - 1) n := by
  have hvTouch := support_faceBoundaryGraph_subset
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega) hv
  simp only [Set.mem_iUnion] at hvTouch
  obtain ⟨c, hcFill, hcFace⟩ := hvTouch
  have hcBox := rlc_twoChannelFullFilledReachSet_subset_connectorRect
    hn gamma gamma' omega hcFill
  simp [cornerFaces] at hcFace
  rcases hcFace with h | h | h | h
  · rw [h, mem_rect]
    rw [mem_rect] at hcBox
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [h, mem_rect]
    rw [mem_rect] at hcBox
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [h, mem_rect]
    rw [mem_rect] at hcBox
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [h, mem_rect]
    rw [mem_rect] at hcBox
    omega


theorem rlc_twoChannelFullPhysical_innerTraceSourceSpliceWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (T : (hypercubicLattice 2).Walk vr vl)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hTBox : ∀ v ∈ T.support,
      v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) :
    ∃ V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)),
      (∀ v ∈ V.support,
        v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧
      (((rlc_ambientCrossingWalk gamma.1).takeUntil
          (rlc_dualReflect x)
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma.1 (rlc_dualReflect x)).2 hxPath)).map
            rlc_dualReflectSymmLatticeHom).support ⊆ V.support ∧
      (((rlc_ambientCrossingWalk gamma'.1).dropUntil
          (rlc_dualReflect y)
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma'.1 (rlc_dualReflect y)).2 hyPath)).map
            rlc_dualReflectSymmLatticeHom).support ⊆ V.support ∧
      qr.support ⊆ V.support ∧
      ql.support ⊆ V.support ∧
      T.support ⊆ V.support ∧
      (∀ v ∈ V.support,
        v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil
          (rlc_dualReflect x)
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma.1 (rlc_dualReflect x)).2 hxPath)).map
              rlc_dualReflectSymmLatticeHom).support ∨
        v ∈ qr.support ∨ v = ur ∨ v = vr ∨
        v ∈ T.support ∨ v = vl ∨ v = ul ∨
        v ∈ ql.support ∨
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
  have hn : 0 < n := by
    have hstartBox := gamma.1.1.2.1
    rw [mem_rect] at hstartBox
    have hstrict := hfaith.right_axis_strict
    omega
  let hle : rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega ≤ hypercubicLattice 2 :=
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
      gamma gamma' omega).trans
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
  let qrL := qr.mapLe hle
  let qlL := ql.reverse.mapLe hle
  let eR : (hypercubicLattice 2).Walk ur vr := hurv.1.toWalk
  let eL : (hypercubicLattice 2).Walk vl ul := hulv.1.symm.toWalk
  let M : (hypercubicLattice 2).Walk x y :=
    ((((qrL.append eR).append T).append eL).append qlL)
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hxWR : rlc_dualReflect x ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (rlc_dualReflect x)).2 hxPath
  have hyWL : rlc_dualReflect y ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_dualReflect y)).2 hyPath
  let pre0 := (WR.takeUntil (rlc_dualReflect x) hxWR).map
    rlc_dualReflectSymmLatticeHom
  let post0 := (WL.dropUntil (rlc_dualReflect y) hyWL).map
    rlc_dualReflectSymmLatticeHom
  have hpreEnd : rlc_dualReflect.symm (rlc_dualReflect x) = x :=
    rlc_dualReflect.symm_apply_apply x
  have hpostStart : rlc_dualReflect.symm (rlc_dualReflect y) = y :=
    rlc_dualReflect.symm_apply_apply y
  let pre : (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm (gamma.1.1 : Site 2)) x :=
    pre0.copy rfl hpreEnd
  let post : (hypercubicLattice 2).Walk y
      (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)) :=
    post0.copy hpostStart rfl
  let V := (pre.append M).append post
  have hboundaryBox {v : Site 2}
      (hv : v ∈ (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
      v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    have h := rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
      hn gamma gamma' omega hv
    rw [mem_rect] at h ⊢
    omega
  have qrBoundary {v : Site 2} (hv : v ∈ qr.support) :
      v ∈ (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hv
    rcases hv with rfl | ⟨e, he, hve⟩
    · exact hurv.mem_support_left
    · induction e using Sym2.inductionOn with
      | _ a b =>
          have hab := (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma' omega) (qr.adj_of_mem_edges he)
          rw [Sym2.mem_iff] at hve
          rcases hve with rfl | rfl
          · exact hab.mem_support_left
          · exact hab.mem_support_right
  have qlBoundary {v : Site 2} (hv : v ∈ ql.support) :
      v ∈ (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hv
    rcases hv with rfl | ⟨e, he, hve⟩
    · exact hulv.mem_support_left
    · induction e using Sym2.inductionOn with
      | _ a b =>
          have hab := (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma' omega) (ql.adj_of_mem_edges he)
          rw [Sym2.mem_iff] at hve
          rcases hve with rfl | rfl
          · exact hab.mem_support_left
          · exact hab.mem_support_right
  have hgoodBox {v : Site 2} (hv : v ∈ qrL.support ∨ v ∈ qlL.support) :
      v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    apply hboundaryBox
    rcases hv with hv | hv
    · apply qrBoundary
      simpa [qrL, SimpleGraph.Walk.support_mapLe_eq_support] using hv
    · apply qlBoundary
      simpa [qlL, SimpleGraph.Walk.support_mapLe_eq_support,
        SimpleGraph.Walk.support_reverse] using hv
  refine ⟨V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    change v ∈ ((pre.append M).append post).support at hv
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with (hvPre | hvM) | hvPost
    · dsimp only [pre] at hvPre
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_map, List.mem_map] at hvPre
      obtain ⟨w, hw, rfl⟩ := hvPre
      have hwWR := WR.support_takeUntil_subset_support hxWR hw
      have hwPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 w).1
          hwWR
      have hwBox := rlc_pathVertex_mem_rect gamma.1 hwPath
      change rlc_dualReflect.symm w ∈
        rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)
      rw [mem_rect] at hwBox ⊢
      simp [rlc_dualReflect, rlc_dualReflectInvFun]
      omega
    · change v ∈
        ((((qrL.append eR).append T).append eL).append qlL).support at hvM
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.mem_support_append_iff] at hvM
      rcases hvM with (((hvQr | hvER) | hvT) | hvEL) | hvQl
      · exact hgoodBox (Or.inl hvQr)
      · have hvEnds : v = ur ∨ v = vr := by simpa [eR] using hvER
        rcases hvEnds with rfl | rfl
        · exact hboundaryBox hurv.mem_support_left
        · exact hboundaryBox hurv.mem_support_right
      · exact hTBox v hvT
      · have hvEnds : v = vl ∨ v = ul := by simpa [eL] using hvEL
        rcases hvEnds with rfl | rfl
        · exact hboundaryBox hulv.mem_support_right
        · exact hboundaryBox hulv.mem_support_left
      · exact hgoodBox (Or.inr hvQl)
    · dsimp only [post] at hvPost
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_map, List.mem_map] at hvPost
      obtain ⟨w, hw, rfl⟩ := hvPost
      have hwWL := WL.support_dropUntil_subset hyWL hw
      have hwPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 w).1
          hwWL
      have hwBox := rlc_pathVertex_mem_rect gamma'.1 hwPath
      change rlc_dualReflect.symm w ∈
        rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)
      rw [mem_rect] at hwBox ⊢
      simp [rlc_dualReflect, rlc_dualReflectInvFun]
      omega
  · intro v hvPre
    change v ∈ ((pre.append M).append post).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    left
    simpa [pre, pre0, SimpleGraph.Walk.support_copy] using hvPre
  · intro v hvPost
    change v ∈ ((pre.append M).append post).support
    rw [SimpleGraph.Walk.mem_support_append_iff]
    right
    simpa [post, post0, SimpleGraph.Walk.support_copy] using hvPost
  · intro v hvQr
    change v ∈ ((pre.append M).append post).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    right
    change v ∈
      ((((qrL.append eR).append T).append eL).append qlL).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inl (Or.inl (Or.inl (by
      simpa [qrL, SimpleGraph.Walk.support_mapLe_eq_support] using hvQr))))
  · intro v hvQl
    change v ∈ ((pre.append M).append post).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    right
    change v ∈
      ((((qrL.append eR).append T).append eL).append qlL).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr (by
      simpa [qlL, SimpleGraph.Walk.support_mapLe_eq_support,
        SimpleGraph.Walk.support_reverse] using hvQl)
  · intro v hvT
    change v ∈ ((pre.append M).append post).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    right
    change v ∈
      ((((qrL.append eR).append T).append eL).append qlL).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inl (Or.inr hvT))
  · intro v hv
    change v ∈ ((pre.append M).append post).support at hv
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with (hvPre | hvM) | hvPost
    · left
      simpa [pre, pre0, SimpleGraph.Walk.support_copy] using hvPre
    · change v ∈
          ((((qrL.append eR).append T).append eL).append qlL).support at hvM
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.mem_support_append_iff] at hvM
      rcases hvM with (((hvQr | hvER) | hvT) | hvEL) | hvQl
      · right; left
        simpa [qrL, SimpleGraph.Walk.support_mapLe_eq_support] using hvQr
      · have hvEnds : v = ur ∨ v = vr := by simpa [eR] using hvER
        rcases hvEnds with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvT))))
      · have hvEnds : v = vl ∨ v = ul := by simpa [eL] using hvEL
        rcases hvEnds with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl rfl)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inl rfl))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl (by
            simpa [qlL, SimpleGraph.Walk.support_mapLe_eq_support,
              SimpleGraph.Walk.support_reverse] using hvQl))))))))
    · right; right; right; right; right; right; right; right
      simpa [post, post0, SimpleGraph.Walk.support_copy] using hvPost
  · intro e he
    change e ∈ ((pre.append M).append post).edges at he
    simp only [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with (hePre | heM) | hePost
    · left
      simpa [pre, pre0, SimpleGraph.Walk.edges_copy] using hePre
    · change e ∈
          ((((qrL.append eR).append T).append eL).append qlL).edges at heM
      simp only [SimpleGraph.Walk.edges_append, List.mem_append] at heM
      rcases heM with (((heQr | heER) | heT) | heEL) | heQl
      · right; left
        simpa [qrL, SimpleGraph.Walk.edges_mapLe_eq_edges] using heQr
      · right; right; left
        simpa [eR] using heER
      · right; right; right; left
        exact heT
      · right; right; right; right; left
        simpa [eL, Sym2.eq_swap] using heEL
      · right; right; right; right; right; left
        simpa [qlL, SimpleGraph.Walk.edges_mapLe_eq_edges,
          SimpleGraph.Walk.edges_reverse] using heQl
    · right; right; right; right; right; right
      simpa [post, post0, SimpleGraph.Walk.edges_copy] using hePost


theorem
    rlc_twoChannelFullPhysical_sourceSplice_BChanging_terminal_or_bridge
    {n : Int} {gamma : RlcRightDiagonalPath n}
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
    {x y ur vr ul vl : Site 2}
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (T : (hypercubicLattice 2).Walk vr vl)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ul vl)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hTBox : ∀ v ∈ T.support,
      v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) :
    ∃ (V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)))
      (f g : Site 2),
      s(f, g) ∈ V.edges ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
        (s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨
          s(f, g) = s(ul, vl)) := by
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  obtain ⟨V, _hVBox, _hpreV, _hpostV, _hqrV, _hqlV, _hTV,
      _hVprov, hVedge⟩ :=
    rlc_twoChannelFullPhysical_innerTraceSourceSpliceWalk
      hfaith qr ql T hurv hulv hxPath hyPath hTBox
  have hrightStartPath : (gamma.1.1 : Site 2) ∈
      rlc_pathVertices gamma.1 :=
    rlc_path_start_mem_vertices gamma.1
  have hleftEndPath : (gamma'.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    rlc_connector_path_end_mem_vertices gamma'.1
  have hrightStartBox : (gamma.1.1 : Site 2) ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_rightPathVertex_mem_connectorBox gamma hrightStartPath
  have hleftEndBox : (gamma'.1.2.1 : Site 2) ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_leftPathVertex_mem_connectorBox gamma' hleftEndPath
  have hstartB : rlc_dualReflect
      (rlc_dualReflect.symm (gamma.1.1 : Site 2)) ∈
        rlc_twoChannelFullPhysicalLiftVertexCut B := by
    rw [rlc_dualReflect.apply_symm_apply]
    exact ⟨hrightStartBox,
      hBright ⟨gamma.1.1, hrightStartBox⟩ hrightStartPath⟩
  have hendB : rlc_dualReflect
      (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)) ∉
        rlc_twoChannelFullPhysicalLiftVertexCut B := by
    rw [rlc_dualReflect.apply_symm_apply]
    rintro ⟨_hbox, hB⟩
    exact hBleft ⟨gamma'.1.2.1, hleftEndBox⟩ hleftEndPath hB
  obtain ⟨f, g, hfgV, hfB, hgB⟩ :=
    rlc_walk_pred_first_exit V
      (fun v => rlc_dualReflect v ∈
        rlc_twoChannelFullPhysicalLiftVertexCut B) hstartB hendB
  let pre := ((rlc_ambientCrossingWalk gamma.1).takeUntil
    (rlc_dualReflect x)
    ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (rlc_dualReflect x)).2 hxPath)).map
        rlc_dualReflectSymmLatticeHom
  let post := ((rlc_ambientCrossingWalk gamma'.1).dropUntil
    (rlc_dualReflect y)
    ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_dualReflect y)).2 hyPath)).map
        rlc_dualReflectSymmLatticeHom
  have preB {v : Site 2} (hv : v ∈ pre.support) :
      rlc_dualReflect v ∈
        rlc_twoChannelFullPhysicalLiftVertexCut B := by
    dsimp only [pre] at hv
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have hwAmbient :=
      (rlc_ambientCrossingWalk gamma.1).support_takeUntil_subset_support
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma.1 (rlc_dualReflect x)).2 hxPath) hw
    have hwPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 w).1
        hwAmbient
    have hwBox := rlc_rightPathVertex_mem_connectorBox gamma hwPath
    change rlc_dualReflect (rlc_dualReflect.symm w) ∈
      rlc_twoChannelFullPhysicalLiftVertexCut B
    rw [rlc_dualReflect.apply_symm_apply]
    exact ⟨hwBox, hBright ⟨w, hwBox⟩ hwPath⟩
  have postNotB {v : Site 2} (hv : v ∈ post.support) :
      rlc_dualReflect v ∉
        rlc_twoChannelFullPhysicalLiftVertexCut B := by
    dsimp only [post] at hv
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have hwAmbient :=
      (rlc_ambientCrossingWalk gamma'.1).support_dropUntil_subset
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 (rlc_dualReflect y)).2 hyPath) hw
    have hwPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 w).1
        hwAmbient
    have hwBox := rlc_leftPathVertex_mem_connectorBox gamma' hwPath
    change rlc_dualReflect (rlc_dualReflect.symm w) ∉
      rlc_twoChannelFullPhysicalLiftVertexCut B
    rw [rlc_dualReflect.apply_symm_apply]
    rintro ⟨_hbox, hB⟩
    exact hBleft ⟨w, hwBox⟩ hwPath hB
  have hlocation : s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨
      s(f, g) = s(ul, vl) := by
    rcases hVedge s(f, g) hfgV with
      hpre | hqr | hright | hT | hleft | hql | hpost
    · have hpre' : s(f, g) ∈ pre.edges := by simpa [pre] using hpre
      exact False.elim (hgB (preB
        (pre.snd_mem_support_of_mem_edges hpre')))
    · have hmono :=
        rlc_twoChannelFullPhysical_goodBoundary_B_monochromatic_of_noPair
          gamma gamma' A B hAright hAleft hnoPair
            (qr.adj_of_mem_edges hqr)
      exact False.elim (hgB (hmono.mp hfB))
    · exact Or.inl hright
    · exact Or.inr (Or.inl hT)
    · exact Or.inr (Or.inr hleft)
    · have hmono :=
        rlc_twoChannelFullPhysical_goodBoundary_B_monochromatic_of_noPair
          gamma gamma' A B hAright hAleft hnoPair
            (ql.adj_of_mem_edges hql)
      exact False.elim (hgB (hmono.mp hfB))
    · have hpost' : s(f, g) ∈ post.edges := by simpa [post] using hpost
      exact False.elim ((postNotB
        (post.fst_mem_support_of_mem_edges hpost')) hfB)
  exact ⟨V, f, g, hfgV,
    ⟨rlc_dualReflect f, rlc_dualReflect g, rfl,
      Or.inl ⟨hfB, hgB⟩⟩, hlocation⟩


theorem rlc_twoChannelFullPhysical_reachableShiftSplice_mem_broadBox
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {ur vr ul vl : Site 2}
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (T : (hypercubicLattice 2).Walk vr vl)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift a = v) :
    ∀ v ∈ T.support,
      v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
  intro v hv
  rcases hTprov v hv with rfl | rfl | rfl | rfl | ⟨a, ha, rfl⟩
  · have hbox :=
      rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
        hn gamma gamma' omega hurv.mem_support_right
    rw [mem_rect] at hbox ⊢
    omega
  · have hbox :=
      rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
        hn gamma gamma' omega hurv.mem_support_left
    rw [mem_rect] at hbox ⊢
    omega
  · have hbox :=
      rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
        hn gamma gamma' omega hulv.mem_support_left
    rw [mem_rect] at hbox ⊢
    omega
  · have hbox :=
      rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
        hn gamma gamma' omega hulv.mem_support_right
    rw [mem_rect] at hbox ⊢
    omega
  · have hbox := rlc_doubleDualShift_mem_translatedRect
      (rlc_twoChannelFullReachSet_subset_box gamma gamma' omega ha)
    rw [mem_rect] at hbox ⊢
    omega


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedBChangingSplice
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
    {z x y ur vr ul vl : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hxz : rlc_dualReflect x = z)
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
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
          gamma gamma' A))).Adj ul vl) :
    ∃ (T : (hypercubicLattice 2).Walk vr vl)
      (V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)))
      (f g : Site 2),
      (∀ v ∈ T.support,
        v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
          ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A),
            phb_doubleDualShift a = v) ∧
      ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
        ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧
      s(f, g) ∈ V.edges ∧
      rlc_twoChannelFullPhysicalEdgeCrossesCut
        (rlc_twoChannelFullPhysicalLiftVertexCut B)
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
      (s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨
        s(f, g) = s(ul, vl)) := by
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega :=
    rlc_twoChannelFullPhysical_noGoodComponent_of_noPair
      gamma gamma' A B hAright hAleft hBright hBleft hnoPair
  obtain ⟨T, hTprov, horder⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice
      hnoGood hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv
  have hTBox :=
    rlc_twoChannelFullPhysical_reachableShiftSplice_mem_broadBox
      hn hurv hulv T hTprov
  obtain ⟨V, f, g, hfgV, hcross, hlocation⟩ :=
    rlc_twoChannelFullPhysical_sourceSplice_BChanging_terminal_or_bridge
      hfaith A B hAright hAleft hBright hBleft hnoPair qr ql T hurv hulv
        hxPath hyPath hTBox
  exact ⟨T, V, f, g, hTprov, horder, hfgV, hcross, hlocation⟩


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_terminalFailure_or_bridge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {x y ur vr ul vl : Site 2}
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
    {T : (hypercubicLattice 2).Walk vr vl} {f g : Site 2}
    (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        s(rlc_dualReflect f, rlc_dualReflect g))
    (hlocation : s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨
      s(f, g) = s(ul, vl)) :
    s(f, g) ∈ T.edges ∨
      (s(f, g) = s(ur, vr) ∧
        RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure
          gamma gamma' B ur vr) ∨
      (s(f, g) = s(ul, vl) ∧
        RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure
          gamma gamma' B ul vl) := by
  rcases hlocation with hright | hbridge | hleft
  · right
    left
    refine ⟨hright, ?_⟩
    apply
      rlc_twoChannelFullPhysical_noPair_exclusiveReflectedLeft_terminalFailure
        gamma gamma' A B hAright hAleft hnoPair hurv hrow.2.1
    have hmap := congrArg (Sym2.map rlc_dualReflect) hright
    simp only [Sym2.map_mk] at hmap
    rw [← hmap]
    exact hcross
  · exact Or.inl hbridge
  · right
    right
    refine ⟨hleft, ?_⟩
    apply
      rlc_twoChannelFullPhysical_noPair_exclusiveReflectedLeft_terminalFailure
        gamma gamma' A B hAright hAleft hnoPair hulv hrow.2.2.2
    have hmap := congrArg (Sym2.map rlc_dualReflect) hleft
    simp only [Sym2.map_mk] at hmap
    rw [← hmap]
    exact hcross


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactTerminalResidue_or_bridge
    {n : Int} (hn : 0 < n) {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {x y ur vr ul vl : Site 2}
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
    {T : (hypercubicLattice 2).Walk vr vl} {f g : Site 2}
    (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        s(rlc_dualReflect f, rlc_dualReflect g))
    (hlocation : s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨
      s(f, g) = s(ul, vl)) :
    s(f, g) ∈ T.edges ∨
      (s(f, g) = s(ur, vr) ∧
        RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
          gamma gamma' A B ur vr) ∨
      (s(f, g) = s(ul, vl) ∧
        RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
          gamma gamma' A B ul vl) := by
  rcases
      rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_terminalFailure_or_bridge
        A B hAright hAleft hnoPair qr ql hrow hurv hulv hcross hlocation with
    hbridge | ⟨hright, hfailure⟩ | ⟨hleft, hfailure⟩
  · exact Or.inl hbridge
  · exact Or.inr (Or.inl ⟨hright,
      rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_exactResidue
        hn gamma gamma' A B hAright hAleft hurv hrow.2.1 hfailure⟩)
  · exact Or.inr (Or.inr ⟨hleft,
      rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_exactResidue
        hn gamma gamma' A B hAright hAleft hulv hrow.2.2.2 hfailure⟩)


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowFour_orderedBChangingSplice
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
    {r x y ur vr ul vl : Site 2}
    (hrRight : r ∈ rlc_pathVertices gamma.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hxAxis : rlc_dualReflect x = (gamma.1.1 : Site 2))
    (hyr : rlc_dualReflect y = rlc_flipX r)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowFour
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ul vl) :
    ∃ (T : (hypercubicLattice 2).Walk vr vl)
      (V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)))
      (f g : Site 2),
      (∀ v ∈ T.support,
        v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
          ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A),
            phb_doubleDualShift a = v) ∧
      (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support.idxOf
            (rlc_dualReflect ul) <
        (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support.idxOf
            (rlc_dualReflect ur) ∧
      s(f, g) ∈ V.edges ∧
      rlc_twoChannelFullPhysicalEdgeCrossesCut
        (rlc_twoChannelFullPhysicalLiftVertexCut B)
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
      (s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨
        s(f, g) = s(ul, vl)) := by
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega :=
    rlc_twoChannelFullPhysical_noGoodComponent_of_noPair
      gamma gamma' A B hAright hAleft hBright hBleft hnoPair
  obtain ⟨T, hTprov, horder⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowFour_orderedSourceSplice
      hnoGood hrRight hxPath hyPath qr ql hxAxis hyr hrow hurv hulv
  have hTBox :=
    rlc_twoChannelFullPhysical_reachableShiftSplice_mem_broadBox
      hn hurv hulv T hTprov
  obtain ⟨V, f, g, hfgV, hcross, hlocation⟩ :=
    rlc_twoChannelFullPhysical_sourceSplice_BChanging_terminal_or_bridge
      hfaith A B hAright hAleft hBright hBleft hnoPair qr ql T hurv hulv
        hxPath hyPath hTBox
  exact ⟨T, V, f, g, hTprov, horder, hfgV, hcross, hlocation⟩


end
end StatMech.Universality
