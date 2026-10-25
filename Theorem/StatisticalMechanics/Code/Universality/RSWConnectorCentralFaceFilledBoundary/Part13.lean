/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_bookFlippedTraceIntersection_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    RlcBookFlippedTraceIntersection gamma gamma' := by
  classical
  let L : Site 2 := gamma'.1.1
  let U : Site 2 := gamma'.1.2.1
  let S : Site 2 := gamma.1.1
  let T : Site 2 := gamma.1.2.1
  let alpha : Int := -2 * n - 1
  let beta : Int := 1
  let bottom : Int := -n - 1
  let top : Int := n + 1
  have hL0 : L 0 = -2 * n := by
    simpa [L] using gamma'.1.1.2.2
  have hU0 : U 0 = 0 := by
    simpa [U] using gamma'.1.2.1.2.2
  have hS0 : S 0 = 0 := by
    simpa [S] using gamma.1.1.2.2
  have hT0 : T 0 = 2 * n := by
    simpa [T] using gamma.1.2.1.2.2
  have hLy : -n ≤ L 1 ∧ L 1 ≤ 0 := by
    have hbox := gamma'.1.1.2.1
    rw [mem_rect] at hbox
    exact ⟨hbox.2.2.1, gamma'.2.1⟩
  have hUy : 0 < U 1 ∧ U 1 ≤ n := by
    have hbox := gamma'.1.2.1.2.1
    rw [mem_rect] at hbox
    exact ⟨hfaith.left_axis_strict, hbox.2.2.2⟩
  have hSy : -n ≤ S 1 ∧ S 1 < 0 := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    exact ⟨hbox.2.2.1, hfaith.right_axis_strict⟩
  have hTy : 0 ≤ T 1 ∧ T 1 ≤ n := by
    have hbox := gamma.1.2.1.2.1
    rw [mem_rect] at hbox
    exact ⟨gamma.2.2, hbox.2.2.2⟩
  have hn : 0 < n := by omega
  have hL : (![-2 * n, L 1] : Site 2) = L := by
    ext i
    fin_cases i <;> simp [hL0]
  have hU : (![0, U 1] : Site 2) = U := by
    ext i
    fin_cases i <;> simp [hU0]
  have hS : (![0, S 1] : Site 2) = S := by
    ext i
    fin_cases i <;> simp [hS0]
  have hflipT : (![-2 * n, T 1] : Site 2) = rlc_flipX T := by
    ext i
    fin_cases i <;> simp [rlc_flipX, rlc_flipXFun, hT0]
  let pre : (hypercubicLattice 2).Walk ![alpha, bottom] L :=
    ((sw_vertSeg alpha bottom (L 1)).append
      (sw_horizSeg (L 1) alpha (-2 * n))).copy rfl hL
  let post : (hypercubicLattice 2).Walk U ![beta, top] :=
    ((sw_horizSeg (U 1) 0 beta).append
      (sw_vertSeg beta (U 1) top)).copy hU rfl
  let leftWalk : (hypercubicLattice 2).Walk L U :=
    rlc_ambientCrossingWalk gamma'.1
  let V : (hypercubicLattice 2).Walk ![alpha, bottom] ![beta, top] :=
    (pre.append leftWalk).append post
  let reflectedRight : (hypercubicLattice 2).Walk (rlc_flipX T) S :=
    ((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse.copy
      rfl (by simpa [S] using (rlc_flipX_eq_self_of_zero hS0))
  let before : (hypercubicLattice 2).Walk
      ![alpha, T 1] (rlc_flipX T) :=
    (sw_horizSeg (T 1) alpha (-2 * n)).copy rfl hflipT
  let after : (hypercubicLattice 2).Walk S ![beta, S 1] :=
    (sw_horizSeg (S 1) 0 beta).copy hS rfl
  let H : (hypercubicLattice 2).Walk ![alpha, T 1] ![beta, S 1] :=
    (before.append reflectedRight).append after
  have hVBox : ∀ z ∈ V.support, z ∈ rect alpha beta bottom top := by
    intro z hz
    dsimp only [V] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hzPre | hzLeft) | hzPost
    · dsimp only [pre] at hzPre
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.mem_support_append_iff] at hzPre
      rcases hzPre with hzVert | hzHoriz
      · rw [sw_vertSeg_mem_support] at hzVert
        obtain ⟨t, ht, rfl⟩ := hzVert
        rw [Set.mem_uIcc] at ht
        simp [mem_rect, alpha, beta, bottom, top]
        omega
      · rw [sw_horizSeg_mem_support] at hzHoriz
        obtain ⟨x, hx, rfl⟩ := hzHoriz
        rw [Set.mem_uIcc] at hx
        simp [mem_rect, alpha, beta, bottom, top]
        omega
    · have hzRect := rlc_pathVertex_mem_rect gamma'.1
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma'.1 z).1 hzLeft)
      rw [mem_rect] at hzRect ⊢
      simp only [alpha, beta, bottom, top]
      omega
    · dsimp only [post] at hzPost
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.mem_support_append_iff] at hzPost
      rcases hzPost with hzHoriz | hzVert
      · rw [sw_horizSeg_mem_support] at hzHoriz
        obtain ⟨x, hx, rfl⟩ := hzHoriz
        rw [Set.mem_uIcc] at hx
        simp [mem_rect, alpha, beta, bottom, top]
        omega
      · rw [sw_vertSeg_mem_support] at hzVert
        obtain ⟨t, ht, rfl⟩ := hzVert
        rw [Set.mem_uIcc] at ht
        simp [mem_rect, alpha, beta, bottom, top]
        omega
  have hHBox : ∀ z ∈ H.support, z ∈ rect alpha beta bottom top := by
    intro z hz
    dsimp only [H] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hzBefore | hzRight) | hzAfter
    · dsimp only [before] at hzBefore
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
      obtain ⟨x, hx, rfl⟩ := hzBefore
      rw [Set.mem_uIcc] at hx
      simp [mem_rect, alpha, beta, bottom, top]
      omega
    · dsimp only [reflectedRight] at hzRight
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
        List.mem_reverse,
        SimpleGraph.Walk.support_map, List.mem_map] at hzRight
      obtain ⟨q, hq, hqz⟩ := hzRight
      change rlc_flipX q = z at hqz
      rw [← hqz]
      have hqRect := rlc_pathVertex_mem_rect gamma.1
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
      rw [mem_rect] at hqRect ⊢
      simp only [alpha, beta, bottom, top]
      simp [rlc_flipX, rlc_flipXFun]
      omega
    · dsimp only [after] at hzAfter
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
      obtain ⟨x, hx, rfl⟩ := hzAfter
      rw [Set.mem_uIcc] at hx
      simp [mem_rect, alpha, beta, bottom, top]
      omega
  have hsep : ArcSeparatingSet {z | z ∈ V.support}
      alpha beta bottom top := by
    apply jec_arcSeparatingSet alpha beta bottom top alpha beta
      (by simp [alpha, beta]; omega) (by simp [bottom, top]; omega)
      (le_refl _) (by omega) (by omega) (le_refl _) V hVBox
    intro z hz
    exact hz
  obtain ⟨z, hzH, hzV⟩ := tpc_two_paths_cross_of_sep hsep
    (hHBox _ H.start_mem_support) (hHBox _ H.end_mem_support)
    (by rfl) (by rfl) H hHBox
  change z ∈ V.support at hzV
  dsimp only [V] at hzV
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hzV
  dsimp only [H] at hzH
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hzH
  rcases hzV with (hzPre | hzLeft) | hzPost
  · dsimp only [pre] at hzPre
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_append_iff] at hzPre
    rcases hzPre with hzPreVert | hzPreHoriz
    · rw [sw_vertSeg_mem_support] at hzPreVert
      obtain ⟨t, ht, rfl⟩ := hzPreVert
      rw [Set.mem_uIcc] at ht
      rcases hzH with (hzBefore | hzRight) | hzAfter
      · dsimp only [before] at hzBefore
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
        obtain ⟨x, hx, heq⟩ := hzBefore
        have heq0 := congrArg (fun q : Site 2 => q 0) heq
        have heq1 := congrArg (fun q : Site 2 => q 1) heq
        simp [alpha] at heq0 heq1
        have hzero : T 1 = 0 ∧ L 1 = 0 := by omega
        refine ⟨T, rlc_connector_path_end_mem_vertices gamma.1, ?_⟩
        have : rlc_flipX T = L := by
          ext i
          fin_cases i <;> simp [rlc_flipX, rlc_flipXFun, hT0, hL0,
            hzero.1, hzero.2]
        rw [this]
        exact rlc_path_start_mem_vertices gamma'.1
      · dsimp only [reflectedRight] at hzRight
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
          List.mem_reverse,
          SimpleGraph.Walk.support_map, List.mem_map] at hzRight
        obtain ⟨q, hq, heq⟩ := hzRight
        change rlc_flipX q = (![alpha, t] : Site 2) at heq
        have hqRect := rlc_pathVertex_mem_rect gamma.1
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
        rw [mem_rect] at hqRect
        have heq0 := congrArg (fun q : Site 2 => q 0) heq
        simp [alpha, rlc_flipX, rlc_flipXFun] at heq0
        omega
      · dsimp only [after] at hzAfter
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
        obtain ⟨x, hx, heq⟩ := hzAfter
        rw [Set.mem_uIcc] at hx
        have heq0 := congrArg (fun q : Site 2 => q 0) heq
        simp at heq0
        omega
    · rw [sw_horizSeg_mem_support] at hzPreHoriz
      obtain ⟨x, hx, heqPre⟩ := hzPreHoriz
      rw [Set.mem_uIcc] at hx
      rcases hzH with (hzBefore | hzRight) | hzAfter
      · dsimp only [before] at hzBefore
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
        obtain ⟨x', hx', heqH⟩ := hzBefore
        have heq1 := congrArg (fun q : Site 2 => q 1)
          (heqPre.symm.trans heqH)
        simp at heq1
        refine ⟨T, rlc_connector_path_end_mem_vertices gamma.1, ?_⟩
        have : rlc_flipX T = L := by
          ext i
          fin_cases i <;> simp [rlc_flipX, rlc_flipXFun, hT0, hL0, heq1]
        rw [this]
        exact rlc_path_start_mem_vertices gamma'.1
      · dsimp only [reflectedRight] at hzRight
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
          List.mem_reverse,
          SimpleGraph.Walk.support_map, List.mem_map] at hzRight
        obtain ⟨q, hq, heqH⟩ := hzRight
        change rlc_flipX q = z at heqH
        have hqRect := rlc_pathVertex_mem_rect gamma.1
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
        rw [mem_rect] at hqRect
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqH.trans heqPre)
        simp [rlc_flipX, rlc_flipXFun] at heq0
        have hq0 : q 0 = 2 * n := by omega
        have heqL : rlc_flipX q = L := by
          ext i
          fin_cases i
          · simp [rlc_flipX, rlc_flipXFun, hq0, hL0]
          · have heq1 := congrArg (fun q : Site 2 => q 1)
                (heqH.trans heqPre)
            simpa [rlc_flipX, rlc_flipXFun] using heq1
        refine ⟨q,
          (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq,
          ?_⟩
        rw [heqL]
        exact rlc_path_start_mem_vertices gamma'.1
      · dsimp only [after] at hzAfter
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
        obtain ⟨x', hx', heqH⟩ := hzAfter
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqPre.symm.trans heqH)
        rw [Set.mem_uIcc] at hx'
        simp at heq0
        omega
  · have hzLeftPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).1 hzLeft
    rcases hzH with (hzBefore | hzRight) | hzAfter
    · dsimp only [before] at hzBefore
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
      obtain ⟨x, hx, heq⟩ := hzBefore
      have hzRect := rlc_pathVertex_mem_rect gamma'.1 hzLeftPath
      rw [Set.mem_uIcc] at hx
      rw [mem_rect] at hzRect
      have heq0 := congrArg (fun q : Site 2 => q 0) heq
      simp at heq0
      have hzEq : z = rlc_flipX T := by
        ext i
        fin_cases i
        · simp [rlc_flipX, rlc_flipXFun, hT0]
          omega
        · simpa [rlc_flipX, rlc_flipXFun] using
            congrArg (fun q : Site 2 => q 1) heq
      refine ⟨T, rlc_connector_path_end_mem_vertices gamma.1, ?_⟩
      rwa [hzEq] at hzLeftPath
    · dsimp only [reflectedRight] at hzRight
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
        List.mem_reverse,
        SimpleGraph.Walk.support_map, List.mem_map] at hzRight
      obtain ⟨q, hq, heq⟩ := hzRight
      change rlc_flipX q = z at heq
      refine ⟨q,
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq,
        ?_⟩
      rwa [heq]
    · dsimp only [after] at hzAfter
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
      obtain ⟨x, hx, heq⟩ := hzAfter
      rw [Set.mem_uIcc] at hx
      have hzRect := rlc_pathVertex_mem_rect gamma'.1 hzLeftPath
      rw [mem_rect] at hzRect
      have heq0 := congrArg (fun q : Site 2 => q 0) heq
      have hz0 : z 0 = 0 := by simp at heq0; omega
      have hzU : z = U := hfaith.left_axis_unique hzLeftPath hz0
      have hzU1 : z 1 = U 1 := congrArg (fun q : Site 2 => q 1) hzU
      have heq1 := congrArg (fun q : Site 2 => q 1) heq
      simp at heq1
      omega
  · dsimp only [post] at hzPost
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_append_iff] at hzPost
    rcases hzPost with hzPostHoriz | hzPostVert
    · rw [sw_horizSeg_mem_support] at hzPostHoriz
      obtain ⟨x, hx, heqPost⟩ := hzPostHoriz
      rw [Set.mem_uIcc] at hx
      rcases hzH with (hzBefore | hzRight) | hzAfter
      · dsimp only [before] at hzBefore
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
        obtain ⟨x', hx', heqH⟩ := hzBefore
        rw [Set.mem_uIcc] at hx'
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqPost.symm.trans heqH)
        simp at heq0
        omega
      · dsimp only [reflectedRight] at hzRight
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
          List.mem_reverse,
          SimpleGraph.Walk.support_map, List.mem_map] at hzRight
        obtain ⟨q, hq, heqH⟩ := hzRight
        change rlc_flipX q = z at heqH
        have hqRect := rlc_pathVertex_mem_rect gamma.1
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
        rw [mem_rect] at hqRect
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqH.trans heqPost)
        simp [rlc_flipX, rlc_flipXFun] at heq0
        have hq0 : q 0 = 0 := by omega
        have hqS : q = S := hfaith.right_axis_unique
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
          hq0
        have hqS1 : q 1 = S 1 := congrArg (fun z : Site 2 => z 1) hqS
        have heq1 := congrArg (fun q : Site 2 => q 1)
          (heqH.trans heqPost)
        simp [rlc_flipX, rlc_flipXFun] at heq1
        omega
      · dsimp only [after] at hzAfter
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
        obtain ⟨x', hx', heqH⟩ := hzAfter
        rw [Set.mem_uIcc] at hx'
        have heq1 := congrArg (fun q : Site 2 => q 1)
          (heqPost.symm.trans heqH)
        simp at heq1
        omega
    · rw [sw_vertSeg_mem_support] at hzPostVert
      obtain ⟨t, ht, heqPost⟩ := hzPostVert
      rw [Set.mem_uIcc] at ht
      rcases hzH with (hzBefore | hzRight) | hzAfter
      · dsimp only [before] at hzBefore
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
        obtain ⟨x, hx, heqH⟩ := hzBefore
        rw [Set.mem_uIcc] at hx
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqPost.symm.trans heqH)
        simp [beta] at heq0
        omega
      · dsimp only [reflectedRight] at hzRight
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
          List.mem_reverse,
          SimpleGraph.Walk.support_map, List.mem_map] at hzRight
        obtain ⟨q, hq, heqH⟩ := hzRight
        change rlc_flipX q = z at heqH
        have hqRect := rlc_pathVertex_mem_rect gamma.1
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
        rw [mem_rect] at hqRect
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqH.trans heqPost)
        simp [beta, rlc_flipX, rlc_flipXFun] at heq0
        omega
      · dsimp only [after] at hzAfter
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
        obtain ⟨x, hx, heqH⟩ := hzAfter
        rw [Set.mem_uIcc] at hx
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqPost.symm.trans heqH)
        have heq1 := congrArg (fun q : Site 2 => q 1)
          (heqPost.symm.trans heqH)
        simp [beta] at heq0 heq1
        omega


theorem rlc_bookFourTraceOrderedSides_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (rightSide : (hypercubicLattice 2).Walk
          (gamma.1.1 : Site 2) (gamma'.1.2.1 : Site 2))
      (leftSide : (hypercubicLattice 2).Walk
          (gamma'.1.2.1 : Site 2) (gamma.1.1 : Site 2)),
      (∀ e ∈ rightSide.edges,
        e ∈ rlc_pathEdges gamma.1 ∨
          e ∈ rlc_reflectedPathEdges gamma'.1) ∧
      (∀ z ∈ rightSide.support, 0 ≤ z 0) ∧
      (∀ e ∈ leftSide.edges,
        e ∈ rlc_pathEdges gamma'.1 ∨
          e ∈ rlc_reflectedPathEdges gamma.1) ∧
      ∀ z ∈ leftSide.support, z 0 ≤ 0 := by
  obtain ⟨p, hpRight, hpFlipLeft⟩ :=
    rlc_bookFlippedTraceIntersection_of_faithful gamma gamma' hfaith
  let q := rlc_flipX p
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hpWR : p ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 p).2 hpRight
  have hqWL : q ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 q).2 hpFlipLeft
  let right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) p :=
    WR.takeUntil p hpWR
  let left : (hypercubicLattice 2).Walk q (gamma'.1.2.1 : Site 2) :=
    (WL.takeUntil q hqWL).reverse.append WL
  have hflipQ : rlc_flipX q = p := by simp [q]
  have hflipUpper : rlc_flipX (gamma'.1.2.1 : Site 2) = gamma'.1.2.1 :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hflipLower : rlc_flipX (gamma.1.1 : Site 2) = gamma.1.1 :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  let flipLeft : (hypercubicLattice 2).Walk p (gamma'.1.2.1 : Site 2) :=
    (left.map rlc_flipXLatticeHom).copy hflipQ hflipUpper
  let flipRightRev : (hypercubicLattice 2).Walk q (gamma.1.1 : Site 2) :=
    (right.map rlc_flipXLatticeHom).reverse.copy rfl hflipLower
  let rightSide := right.append flipLeft
  let leftSide := left.reverse.append flipRightRev
  have hrightEdges : ∀ e ∈ right.edges, e ∈ rlc_pathEdges gamma.1 := by
    intro e he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1
    exact WR.edges_takeUntil_subset hpWR he
  have hleftEdges : ∀ e ∈ left.edges, e ∈ rlc_pathEdges gamma'.1 := by
    intro e he
    dsimp only [left] at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
    rcases he with he | he
    · exact WL.edges_takeUntil_subset hqWL he
    · exact he
  have hrightSupport : ∀ z ∈ right.support, 0 ≤ z 0 := by
    intro z hz
    have hzWR : z ∈ WR.support := by
      change z ∈ (WR.takeUntil p hpWR).support at hz
      exact WR.support_takeUntil_subset_support hpWR hz
    have hzPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).1 hzWR
    have hzRect := rlc_pathVertex_mem_rect gamma.1 hzPath
    rw [mem_rect] at hzRect
    exact hzRect.1
  have hleftSupport : ∀ z ∈ left.support, z 0 ≤ 0 := by
    intro z hz
    dsimp only [left] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    have hzWL : z ∈ WL.support := hz.elim
      (fun hz => WL.support_takeUntil_subset_support hqWL hz) id
    have hzPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).1 hzWL
    have hzRect := rlc_pathVertex_mem_rect gamma'.1 hzPath
    rw [mem_rect] at hzRect
    exact hzRect.2.1
  refine ⟨rightSide, leftSide, ?_, ?_, ?_, ?_⟩
  · intro e he
    change e ∈ (right.append flipLeft).edges at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact Or.inl (hrightEdges e he)
    · right
      dsimp only [flipLeft] at he
      rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      rw [rlc_reflectedPathEdges, Finset.mem_image]
      exact ⟨e0, hleftEdges e0 he0, rfl⟩
  · intro z hz
    change z ∈ (right.append flipLeft).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact hrightSupport z hz
    · dsimp only [flipLeft] at hz
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z0, hz0, rfl⟩ := hz
      have hz0Bound := hleftSupport z0 hz0
      change 0 ≤ -z0 0
      omega
  · intro e he
    change e ∈ (left.reverse.append flipRightRev).edges at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rcases he with he | he
    · exact Or.inl (hleftEdges e he)
    · right
      dsimp only [flipRightRev] at he
      rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse,
        List.mem_reverse, SimpleGraph.Walk.edges_map] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      rw [rlc_reflectedPathEdges, Finset.mem_image]
      exact ⟨e0, hrightEdges e0 he0, rfl⟩
  · intro z hz
    change z ∈ (left.reverse.append flipRightRev).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    rcases hz with hz | hz
    · exact hleftSupport z hz
    · dsimp only [flipRightRev] at hz
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z0, hz0, rfl⟩ := hz
      have hz0Bound := hrightSupport z0 hz0
      change -z0 0 ≤ 0
      omega


theorem rlc_connectorBarrier_positive_classify {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz0 : 0 < z 0)
    (hz : z ∈ rlc_connectorBarrier gamma gamma') :
    z ∈ rlc_pathVertices gamma.1 ∨
      ∃ w ∈ rlc_pathVertices gamma'.1, z = rlc_flipX w := by
  simp only [rlc_connectorBarrier, Finset.mem_union] at hz
  rcases hz with ((hright | hleft) | hflipRight) | hflipLeft
  · exact Or.inl hright
  · have hzRect := rlc_pathVertex_mem_rect gamma'.1 hleft
    rw [mem_rect] at hzRect
    omega
  · obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hflipRight
    have hwRect := rlc_pathVertex_mem_rect gamma.1 hw
    rw [mem_rect] at hwRect
    have hcoord := congrArg (fun q : Site 2 => q 0) hwz
    simp [rlc_flipX, rlc_flipXFun] at hcoord
    omega
  · obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hflipLeft
    exact Or.inr ⟨w, hw, hwz.symm⟩


theorem rlc_connectorBarrier_negative_classify {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz0 : z 0 < 0)
    (hz : z ∈ rlc_connectorBarrier gamma gamma') :
    z ∈ rlc_pathVertices gamma'.1 ∨
      ∃ w ∈ rlc_pathVertices gamma.1, z = rlc_flipX w := by
  simp only [rlc_connectorBarrier, Finset.mem_union] at hz
  rcases hz with ((hright | hleft) | hflipRight) | hflipLeft
  · have hzRect := rlc_pathVertex_mem_rect gamma.1 hright
    rw [mem_rect] at hzRect
    omega
  · exact Or.inl hleft
  · obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hflipRight
    exact Or.inr ⟨w, hw, hwz.symm⟩
  · obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hflipLeft
    have hwRect := rlc_pathVertex_mem_rect gamma'.1 hw
    rw [mem_rect] at hwRect
    have hcoord := congrArg (fun q : Site 2 => q 0) hwz
    simp [rlc_flipX, rlc_flipXFun] at hcoord
    omega


theorem rlc_connectorBarrier_original_or_strict_reflected {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorBarrier gamma gamma') :
    z ∈ rlc_pathVertices gamma.1 ∨
      z ∈ rlc_pathVertices gamma'.1 ∨
      (0 < z 0 ∧ ∃ w ∈ rlc_pathVertices gamma'.1, z = rlc_flipX w) ∨
      (z 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1, z = rlc_flipX w) := by
  rcases lt_trichotomy (z 0) 0 with hzNeg | hzZero | hzPos
  · rcases rlc_connectorBarrier_negative_classify
      gamma gamma' hzNeg hz with hzLeft | hzFlipRight
    · exact Or.inr (Or.inl hzLeft)
    · exact Or.inr (Or.inr (Or.inr ⟨hzNeg, hzFlipRight⟩))
  · have hzEq : z = (![0, z 1] : Site 2) := by
      ext i
      fin_cases i
      · simpa using hzZero
      · rfl
    have hzAxis : (![0, z 1] : Site 2) ∈
        rlc_connectorBarrier gamma gamma' := by
      rwa [← hzEq]
    rcases (rlc_axis_mem_connectorBarrier_iff
      gamma gamma' (z 1)).1 hzAxis with hzRight | hzLeft
    · exact Or.inl (by rwa [hzEq])
    · exact Or.inr (Or.inl (by rwa [hzEq]))
  · rcases rlc_connectorBarrier_positive_classify
      gamma gamma' hzPos hz with hzRight | hzFlipLeft
    · exact Or.inl hzRight
    · exact Or.inr (Or.inr (Or.inl ⟨hzPos, hzFlipLeft⟩))


theorem rlc_reflectedLeft_hit_sourceNE_not_filled {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u w : Site 2} (hw : w ∈ rlc_pathVertices gamma'.1)
    (hu : rlc_dualReflect u = rlc_flipX w) :
    (![u 0 + 1, u 1 + 1] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
  have hcorner : (![u 0 + 1, u 1 + 1] : Site 2) = w := by
    have h0 := congrArg (fun z : Site 2 => z 0) hu
    have h1 := congrArg (fun z : Site 2 => z 1) hu
    ext i
    fin_cases i <;>
      simp [rlc_dualReflect, rlc_dualReflectFun,
        rlc_flipX, rlc_flipXFun] at h0 h1 ⊢ <;>
      omega
  rw [hcorner]
  have hwExt := rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
    gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno hw
  simpa only [rlc_connectorCentralFaceFilledReachSet,
    Set.mem_compl_iff, not_not] using hwExt


theorem rlc_reflectedRight_hit_sourceNE_mem_filled {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u w : Site 2} (hw : w ∈ rlc_pathVertices gamma.1)
    (hu : rlc_dualReflect u = rlc_flipX w) :
    (![u 0 + 1, u 1 + 1] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
  have hcorner : (![u 0 + 1, u 1 + 1] : Site 2) = w := by
    have h0 := congrArg (fun z : Site 2 => z 0) hu
    have h1 := congrArg (fun z : Site 2 => z 1) hu
    ext i
    fin_cases i <;>
      simp [rlc_dualReflect, rlc_dualReflectFun,
        rlc_flipX, rlc_flipXFun] at h0 h1 ⊢ <;>
      omega
  rw [hcorner]
  exact rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho
    (rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho hw)


theorem rlc_faceBoundary_step_of_NE_not_mem
    (H : Set (Site 2)) {u v : Site 2}
    (huv : (faceBoundaryGraph H).Adj u v)
    (hne : (![u 0 + 1, u 1 + 1] : Site 2) ∉ H) :
    (v = ![u 0 + 1, u 1] ∧
        (![u 0 + 1, u 1] : Site 2) ∈ H) ∨
      v = ![u 0 - 1, u 1] ∨
      (v = ![u 0, u 1 + 1] ∧
        (![u 0, u 1 + 1] : Site 2) ∈ H) ∨
      v = ![u 0, u 1 - 1] := by
  rcases face_adj_dir huv.1 with rfl | rfl | rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have hbd := huv.2
    have hshared : sharedPrimalEdge u ![u 0 + 1, u 1] =
        s((![u 0 + 1, u 1] : Site 2), ![u 0 + 1, u 1 + 1]) := by
      simp [sharedPrimalEdge]
    rw [hshared, bdEdge_mk] at hbd
    exact hbd.mpr hne
  · exact Or.inr (Or.inl rfl)
  · right; right; left
    refine ⟨rfl, ?_⟩
    have hbd := huv.2
    have hshared : sharedPrimalEdge u ![u 0, u 1 + 1] =
        s((![u 0, u 1 + 1] : Site 2), ![u 0 + 1, u 1 + 1]) := by
      simp [sharedPrimalEdge]
    rw [hshared, bdEdge_mk] at hbd
    exact hbd.mpr hne
  · exact Or.inr (Or.inr (Or.inr rfl))


theorem rlc_faceBoundary_step_of_NE_mem
    (H : Set (Site 2)) {u v : Site 2}
    (huv : (faceBoundaryGraph H).Adj u v)
    (hne : (![u 0 + 1, u 1 + 1] : Site 2) ∈ H) :
    (v = ![u 0 + 1, u 1] ∧
        (![u 0 + 1, u 1] : Site 2) ∉ H) ∨
      v = ![u 0 - 1, u 1] ∨
      (v = ![u 0, u 1 + 1] ∧
        (![u 0, u 1 + 1] : Site 2) ∉ H) ∨
      v = ![u 0, u 1 - 1] := by
  rcases face_adj_dir huv.1 with rfl | rfl | rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have hbd := huv.2
    have hshared : sharedPrimalEdge u ![u 0 + 1, u 1] =
        s((![u 0 + 1, u 1] : Site 2), ![u 0 + 1, u 1 + 1]) := by
      simp [sharedPrimalEdge]
    rw [hshared, bdEdge_mk] at hbd
    exact fun hse => (hbd.mp hse) hne
  · exact Or.inr (Or.inl rfl)
  · right; right; left
    refine ⟨rfl, ?_⟩
    have hbd := huv.2
    have hshared : sharedPrimalEdge u ![u 0, u 1 + 1] =
        s((![u 0, u 1 + 1] : Site 2), ![u 0 + 1, u 1 + 1]) := by
      simp [sharedPrimalEdge]
    rw [hshared, bdEdge_mk] at hbd
    exact fun hnw => (hbd.mp hnw) hne
  · exact Or.inr (Or.inr (Or.inr rfl))


theorem rlc_reflectedHit_sharedPrimalEdge_right {u w : Site 2}
    (hu : rlc_dualReflect u = rlc_flipX w) :
    sharedPrimalEdge u ![u 0 + 1, u 1] =
      s((![w 0, w 1 - 1] : Site 2), w) := by
  have h0 := congrArg (fun z : Site 2 => z 0) hu
  have h1 := congrArg (fun z : Site 2 => z 1) hu
  simp [rlc_dualReflect, rlc_dualReflectFun,
    rlc_flipX, rlc_flipXFun] at h0 h1
  rw [show sharedPrimalEdge u ![u 0 + 1, u 1] =
      s((![u 0 + 1, u 1] : Site 2), ![u 0 + 1, u 1 + 1]) by
        simp [sharedPrimalEdge]]
  rw [Sym2.eq_iff]
  left
  constructor <;> ext i <;> fin_cases i <;> simp <;> omega

theorem rlc_reflectedHit_sharedPrimalEdge_top {u w : Site 2}
    (hu : rlc_dualReflect u = rlc_flipX w) :
    sharedPrimalEdge u ![u 0, u 1 + 1] =
      s((![w 0 - 1, w 1] : Site 2), w) := by
  have h0 := congrArg (fun z : Site 2 => z 0) hu
  have h1 := congrArg (fun z : Site 2 => z 1) hu
  simp [rlc_dualReflect, rlc_dualReflectFun,
    rlc_flipX, rlc_flipXFun] at h0 h1
  rw [show sharedPrimalEdge u ![u 0, u 1 + 1] =
      s((![u 0, u 1 + 1] : Site 2), ![u 0 + 1, u 1 + 1]) by
        simp [sharedPrimalEdge]]
  rw [Sym2.eq_iff]
  left
  constructor <;> ext i <;> fin_cases i <;> simp <;> omega

theorem rlc_reflectedHit_sharedPrimalEdge_left {u w : Site 2}
    (hu : rlc_dualReflect u = rlc_flipX w) :
    sharedPrimalEdge u ![u 0 - 1, u 1] =
      s((![w 0 - 1, w 1 - 1] : Site 2), ![w 0 - 1, w 1]) := by
  have h0 := congrArg (fun z : Site 2 => z 0) hu
  have h1 := congrArg (fun z : Site 2 => z 1) hu
  simp [rlc_dualReflect, rlc_dualReflectFun,
    rlc_flipX, rlc_flipXFun] at h0 h1
  rw [show sharedPrimalEdge u ![u 0 - 1, u 1] =
      s((![u 0, u 1] : Site 2), ![u 0, u 1 + 1]) by
        simp [sharedPrimalEdge]; omega]
  rw [Sym2.eq_iff]
  left
  constructor <;> ext i <;> fin_cases i <;> simp <;> omega

theorem rlc_reflectedHit_sharedPrimalEdge_bottom {u w : Site 2}
    (hu : rlc_dualReflect u = rlc_flipX w) :
    sharedPrimalEdge u ![u 0, u 1 - 1] =
      s((![w 0 - 1, w 1 - 1] : Site 2), ![w 0, w 1 - 1]) := by
  have h0 := congrArg (fun z : Site 2 => z 0) hu
  have h1 := congrArg (fun z : Site 2 => z 1) hu
  simp [rlc_dualReflect, rlc_dualReflectFun,
    rlc_flipX, rlc_flipXFun] at h0 h1
  rw [show sharedPrimalEdge u ![u 0, u 1 - 1] =
      s((![u 0, u 1] : Site 2), ![u 0 + 1, u 1]) by
        simp [sharedPrimalEdge]]
  rw [Sym2.eq_iff]
  left
  constructor <;> ext i <;> fin_cases i <;> simp <;> omega


theorem rlc_reflectedHit_boundary_step_ne_right_of_south_exposed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v w : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hu : rlc_dualReflect u = rlc_flipX w)
    (hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    v ≠ ![u 0 + 1, u 1] := by
  intro hv
  subst v
  exact (rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
    gamma gamma' rho hno huv)
      ((rlc_reflectedHit_sharedPrimalEdge_right hu).symm ▸ hsouth)


theorem rlc_reflectedHit_boundary_step_ne_top_of_west_exposed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v w : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hu : rlc_dualReflect u = rlc_flipX w)
    (hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    v ≠ ![u 0, u 1 + 1] := by
  intro hv
  subst v
  exact (rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
    gamma gamma' rho hno huv)
      ((rlc_reflectedHit_sharedPrimalEdge_top hu).symm ▸ hwest)


theorem rlc_pathVertex_incident_edge_of_ne_finish
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {w : Site 2} (hw : w ∈ rlc_pathVertices tau)
    (hne : w ≠ (tau.2.1 : Site 2)) :
    ∃ r : Site 2, s(w, r) ∈ rlc_pathEdges tau := by
  let W := rlc_ambientCrossingWalk tau
  have hwW : w ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau w).2 hw
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hwW
  rcases hwW with hwEnd | ⟨e, he, hwe⟩
  · exact False.elim (hne hwEnd)
  · induction e using Sym2.inductionOn with
    | _ x y =>
        rw [Sym2.mem_iff] at hwe
        rcases hwe with rfl | rfl
        · exact ⟨y, rlc_ambientCrossingWalk_edge_mem_pathEdges tau he⟩
        · exact ⟨x, by
            simpa [Sym2.eq_swap] using
              (rlc_ambientCrossingWalk_edge_mem_pathEdges tau he)⟩


theorem rlc_reflectedPathEdge_endpoint_mem_vertices
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_reflectedPathEdges tau)
    {z : Site 2} (hz : z ∈ e) :
    ∃ w ∈ rlc_pathVertices tau, z = rlc_flipX w := by
  rw [rlc_reflectedPathEdges, Finset.mem_image] at he
  obtain ⟨e0, he0, rfl⟩ := he
  induction e0 using Sym2.inductionOn with
  | _ x y =>
      rw [Sym2.map_mk, Sym2.mem_iff] at hz
      have hends := rlc_pathEdge_endpoints_mem_vertices tau he0
      rcases hz with rfl | rfl
      · exact ⟨x, hends.1, rfl⟩
      · exact ⟨y, hends.2, rfl⟩


theorem rlc_mem_pathEdges_of_reflected_mk
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {x y : Site 2}
    (he : s(rlc_flipX x, rlc_flipX y) ∈ rlc_reflectedPathEdges tau) :
    s(x, y) ∈ rlc_pathEdges tau := by
  rw [rlc_reflectedPathEdges, Finset.mem_image] at he
  obtain ⟨e, he, heq⟩ := he
  have hmap := congrArg (Sym2.map rlc_flipX) heq
  have hinv : e = s(x, y) := by
    induction e using Sym2.inductionOn with
    | _ u v =>
        simpa [Sym2.map_mk, rlc_flipX_involutive] using hmap
  simpa [← hinv] using he


theorem rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorFourTraceEdges gamma gamma')
    {z : Site 2} (hz : z ∈ e)
    (hzRight : z ∉ rlc_pathVertices gamma.1)
    (hzLeft : z ∉ rlc_pathVertices gamma'.1)
    (hzFlipRight : ¬ ∃ w ∈ rlc_pathVertices gamma.1,
      z = rlc_flipX w) :
    e ∈ rlc_reflectedPathEdges gamma'.1 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [rlc_connectorFourTraceEdges, Finset.mem_union] at he
      rcases he with horiginal | hreflected
      · rw [Finset.mem_union] at horiginal
        rcases horiginal with hright | hleft
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
          rw [Sym2.mem_iff] at hz
          exact False.elim (hz.elim (fun h => hzRight (h ▸ hends.1))
            (fun h => hzRight (h ▸ hends.2)))
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
          rw [Sym2.mem_iff] at hz
          exact False.elim (hz.elim (fun h => hzLeft (h ▸ hends.1))
            (fun h => hzLeft (h ▸ hends.2)))
      · rw [rlc_connectorReflectedTraceEdges, Finset.mem_union] at hreflected
        rcases hreflected with hflipRight | hflipLeft
        · exact False.elim (hzFlipRight
            (rlc_reflectedPathEdge_endpoint_mem_vertices
              gamma.1 hflipRight hz))
        · exact hflipLeft


theorem rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorFourTraceEdges gamma gamma')
    {z : Site 2} (hz : z ∈ e)
    (hzRight : z ∉ rlc_pathVertices gamma.1)
    (hzLeft : z ∉ rlc_pathVertices gamma'.1)
    (hzFlipLeft : ¬ ∃ w ∈ rlc_pathVertices gamma'.1,
      z = rlc_flipX w) :
    e ∈ rlc_reflectedPathEdges gamma.1 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [rlc_connectorFourTraceEdges, Finset.mem_union] at he
      rcases he with horiginal | hreflected
      · rw [Finset.mem_union] at horiginal
        rcases horiginal with hright | hleft
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
          rw [Sym2.mem_iff] at hz
          exact False.elim (hz.elim (fun h => hzRight (h ▸ hends.1))
            (fun h => hzRight (h ▸ hends.2)))
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
          rw [Sym2.mem_iff] at hz
          exact False.elim (hz.elim (fun h => hzLeft (h ▸ hends.1))
            (fun h => hzLeft (h ▸ hends.2)))
      · rw [rlc_connectorReflectedTraceEdges, Finset.mem_union] at hreflected
        rcases hreflected with hflipRight | hflipLeft
        · exact hflipRight
        · exact False.elim (hzFlipLeft
            (rlc_reflectedPathEdge_endpoint_mem_vertices
              gamma'.1 hflipLeft hz))


theorem rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') (k : Int) :
    s((![0, k - 1] : Site 2), ![0, k]) ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
  intro he
  have hlow := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
    gamma gamma' he (Sym2.mem_mk_left _ _)
  have hupp := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
    gamma gamma' he (Sym2.mem_mk_right _ _)
  rcases rlc_fourTrace_axis_vertex_height_eq_endpoint
      gamma gamma' hfaith (k - 1) hlow with hlo | hlo <;>
    rcases rlc_fourTrace_axis_vertex_height_eq_endpoint
      gamma gamma' hfaith k hupp with hup | hup <;>
    have hs := hfaith.right_axis_strict <;>
    have hu := hfaith.left_axis_strict <;>
    omega


theorem rlc_bookFourTraceAxisLoop_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      (gamma.1.1 : Site 2) ∈ c.support ∧
        (gamma'.1.2.1 : Site 2) ∈ c.support ∧
        (∀ e ∈ c.edges,
          e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
        (∀ k : Int,
          (gamma.1.1 : Site 2) 1 < k →
          k ≤ (gamma'.1.2.1 : Site 2) 1 →
          ¬ Even (jec_rayCount (![1, k] : Site 2) c)) := by
  obtain ⟨p, hpRight, hpFlipLeft⟩ :=
    rlc_bookFlippedTraceIntersection_of_faithful gamma gamma' hfaith
  let q := rlc_flipX p
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hpWR : p ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 p).2 hpRight
  have hqWL : q ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 q).2 hpFlipLeft
  let right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) p :=
    WR.takeUntil p hpWR
  let left : (hypercubicLattice 2).Walk q (gamma'.1.2.1 : Site 2) :=
    (WL.takeUntil q hqWL).reverse.append WL
  have hflipQ : rlc_flipX q = p := by simp [q]
  have hflipUpper : rlc_flipX (gamma'.1.2.1 : Site 2) = gamma'.1.2.1 :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hflipLower : rlc_flipX (gamma.1.1 : Site 2) = gamma.1.1 :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  let flipLeft : (hypercubicLattice 2).Walk p (gamma'.1.2.1 : Site 2) :=
    (left.map rlc_flipXLatticeHom).copy hflipQ hflipUpper
  let flipRightRev : (hypercubicLattice 2).Walk q (gamma.1.1 : Site 2) :=
    (right.map rlc_flipXLatticeHom).reverse.copy rfl hflipLower
  let rightHalf := right.append flipLeft
  let leftHalf := left.reverse.append flipRightRev
  let c := rightHalf.append leftHalf
  have hrightEdges : ∀ e ∈ right.edges, e ∈ rlc_pathEdges gamma.1 := by
    intro e he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1
    exact WR.edges_takeUntil_subset hpWR he
  have hleftEdges : ∀ e ∈ left.edges, e ∈ rlc_pathEdges gamma'.1 := by
    intro e he
    dsimp only [left] at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
    rcases he with he | he
    · exact WL.edges_takeUntil_subset hqWL he
    · exact he
  have hflipLeftEdges : ∀ e ∈ flipLeft.edges,
      e ∈ rlc_reflectedPathEdges gamma'.1 := by
    intro e he
    dsimp only [flipLeft] at he
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    rw [rlc_reflectedPathEdges, Finset.mem_image]
    exact ⟨e0, hleftEdges e0 he0, rfl⟩
  have hflipRightEdges : ∀ e ∈ flipRightRev.edges,
      e ∈ rlc_reflectedPathEdges gamma.1 := by
    intro e he
    dsimp only [flipRightRev] at he
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse, SimpleGraph.Walk.edges_map] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    rw [rlc_reflectedPathEdges, Finset.mem_image]
    exact ⟨e0, hrightEdges e0 he0, rfl⟩
  refine ⟨c, c.start_mem_support, ?_, ?_, ?_⟩
  · dsimp only [c]
    rw [SimpleGraph.Walk.mem_support_append_iff,
      show rightHalf = right.append flipLeft from rfl,
      SimpleGraph.Walk.mem_support_append_iff,
      show leftHalf = left.reverse.append flipRightRev from rfl]
    exact Or.inl (Or.inr flipLeft.end_mem_support)
  · intro e he
    dsimp only [c] at he
    change e ∈ (rightHalf.append leftHalf).edges at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    change e ∈ (right.append flipLeft).edges ∨
      e ∈ (left.reverse.append flipRightRev).edges at he
    simp only [SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rw [rlc_connectorFourTraceEdges,
      rlc_connectorReflectedTraceEdges]
    rcases he with (he | he) | (he | he)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (hrightEdges e he))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (hflipLeftEdges e he))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (hleftEdges e he))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (hflipRightEdges e he))
  · intro k hkLower hkUpper
    have hrightSupport : ∀ z ∈ right.support, 0 ≤ z 0 := by
      intro z hz
      have hzWR : z ∈ WR.support := by
        change z ∈ (WR.takeUntil p hpWR).support at hz
        exact WR.support_takeUntil_subset_support hpWR hz
      have hzPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).1 hzWR
      have hzRect := rlc_pathVertex_mem_rect gamma.1 hzPath
      rw [mem_rect] at hzRect
      exact hzRect.1
    have hleftSupport : ∀ z ∈ left.support, z 0 ≤ 0 := by
      intro z hz
      dsimp only [left] at hz
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse] at hz
      have hzWL : z ∈ WL.support := by
        rcases hz with hz | hz
        · exact WL.support_takeUntil_subset_support hqWL (by simpa using hz)
        · exact hz
      have hzPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).1 hzWL
      have hzRect := rlc_pathVertex_mem_rect gamma'.1 hzPath
      rw [mem_rect] at hzRect
      exact hzRect.2.1
    have hflipLeftSupport : ∀ z ∈ flipLeft.support, 0 ≤ z 0 := by
      intro z hz
      dsimp only [flipLeft] at hz
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z0, hz0, rfl⟩ := hz
      have hz0Bound := hleftSupport z0 hz0
      change 0 ≤ -z0 0
      omega
    have hflipRightSupport : ∀ z ∈ flipRightRev.support, z 0 ≤ 0 := by
      intro z hz
      dsimp only [flipRightRev] at hz
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z0, hz0, rfl⟩ := hz
      have hz0Bound := hrightSupport z0 hz0
      change -z0 0 ≤ 0
      omega
    have hrightHalfSupport : ∀ z ∈ rightHalf.support, 0 ≤ z 0 := by
      intro z hz
      change z ∈ (right.append flipLeft).support at hz
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      exact hz.elim (hrightSupport z) (hflipLeftSupport z)
    have hleftHalfSupport : ∀ z ∈ leftHalf.support, z 0 ≤ 0 := by
      intro z hz
      change z ∈ (left.reverse.append flipRightRev).support at hz
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
      exact hz.elim (hleftSupport z) (hflipRightSupport z)
    have hrightHalfFour : ∀ e ∈ rightHalf.edges,
        e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
      intro e he
      change e ∈ (right.append flipLeft).edges at he
      rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
      rw [rlc_connectorFourTraceEdges,
        rlc_connectorReflectedTraceEdges]
      rcases he with he | he
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (hrightEdges e he))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (hflipLeftEdges e he))
    have hrightRay : jec_rayCount (![1, k] : Site 2) rightHalf = 0 := by
      rw [jec_rayCount, List.countP_eq_zero]
      intro e he
      simp only [decide_eq_true_eq]
      intro hray
      induction e using Sym2.inductionOn with
      | _ u v =>
          have hu0 := hrightHalfSupport u
            (rightHalf.fst_mem_support_of_mem_edges he)
          have hv0 := hrightHalfSupport v
            (rightHalf.snd_mem_support_of_mem_edges he)
          have hfour := hrightHalfFour s(u, v) he
          rw [jec_rayEdge_mk] at hray
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hray
          rcases hray with ⟨⟨huv0, hcol⟩,
              ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩⟩
          · have huEq : u = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k hfour
          · have huEq : u = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k (by
                simpa [Sym2.eq_swap] using hfour)
    have hleftRay : jec_rayCount (![1, k] : Site 2) leftHalf =
        crossCount (jec_belowSet k) leftHalf := by
      apply jec_ray_eq_below
      intro z hz
      have hz0 := hleftHalfSupport z hz
      simpa using hz0
    have hleftOdd : ¬ Even (jec_rayCount (![1, k] : Site 2) leftHalf) := by
      rw [hleftRay]
      intro heven
      have hsame := (crossCount_parity (jec_belowSet k) leftHalf).mp heven
      have hupperNot : (gamma'.1.2.1 : Site 2) ∉ jec_belowSet k := by
        simp [jec_belowSet]
        omega
      have hlowerIn : (gamma.1.1 : Site 2) ∈ jec_belowSet k := by
        simp [jec_belowSet]
        omega
      exact hupperNot (hsame.mpr hlowerIn)
    change ¬ Even (jec_rayCount (![1, k] : Site 2)
      (rightHalf.append leftHalf))
    rw [jec_rayCount_append, hrightRay, zero_add]
    exact hleftOdd


theorem rlc_bookFourTraceAxisLoop_zeroRay_odd_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      (∀ e ∈ c.edges,
        e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
      ∀ k : Int,
        (gamma.1.1 : Site 2) 1 < k →
        k ≤ (gamma'.1.2.1 : Site 2) 1 →
        ¬ Even (jec_rayCount (![0, k] : Site 2) c) := by
  obtain ⟨c, _hS, _hU, hcEdges, hcOdd⟩ :=
    rlc_bookFourTraceAxisLoop_of_faithful gamma gamma' hfaith
  refine ⟨c, hcEdges, ?_⟩
  intro k hkLower hkUpper
  have heq : jec_rayCount (![0, k] : Site 2) c =
      jec_rayCount (![1, k] : Site 2) c := by
    rw [jec_rayCount, jec_rayCount]
    apply List.countP_congr
    intro e he
    simp only [decide_eq_true_eq]
    induction e using Sym2.inductionOn with
    | _ u v =>
        rw [jec_rayEdge_mk, jec_rayEdge_mk]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        constructor
        · rintro ⟨⟨huv0, hcol⟩, hrow⟩
          exact ⟨⟨huv0, by omega⟩, hrow⟩
        · rintro hright
          by_contra hleft
          have hcol : u 0 = 0 ∧ v 0 = 0 := by
            rcases hright with ⟨⟨huv0, hbound⟩, hrow⟩
            push Not at hleft
            have huNonneg : 0 ≤ u 0 := by omega
            exact ⟨by omega, by omega⟩
          rcases hright with ⟨⟨huv0, _hbound⟩,
              ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩⟩
          · have huEq : u = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k (by
                rw [← huEq, ← hvEq]
                exact hcEdges s(u, v) he)
          · have huEq : u = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k (by
                rw [← hvEq, ← huEq]
                simpa [Sym2.eq_swap] using hcEdges s(u, v) he)
  rw [heq]
  exact hcOdd k hkLower hkUpper


theorem rlc_bookFourTraceAxisLoop_zeroRay_parity_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      (∀ e ∈ c.edges,
        e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
      (∀ k : Int,
        (gamma.1.1 : Site 2) 1 < k →
        k ≤ (gamma'.1.2.1 : Site 2) 1 →
        ¬ Even (jec_rayCount (![0, k] : Site 2) c)) ∧
      ∀ k : Int,
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          (gamma'.1.2.1 : Site 2) 1 < k) →
        Even (jec_rayCount (![0, k] : Site 2) c) := by
  obtain ⟨rightSide, leftSide, hrEdges, hrSupport, hlEdges, hlSupport⟩ :=
    rlc_bookFourTraceOrderedSides_of_faithful gamma gamma' hfaith
  let c := rightSide.append leftSide
  have hrFour : ∀ e ∈ rightSide.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    rcases hrEdges e he with he | he
    · rw [rlc_connectorFourTraceEdges]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
    · rw [rlc_connectorFourTraceEdges,
        rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_right _ he)
  have hlFour : ∀ e ∈ leftSide.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    rcases hlEdges e he with he | he
    · rw [rlc_connectorFourTraceEdges]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
    · rw [rlc_connectorFourTraceEdges,
        rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ he)
  have hcFour : ∀ e ∈ c.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    dsimp only [c] at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    exact he.elim (hrFour e) (hlFour e)
  have ray_eq (k : Int) :
      jec_rayCount (![0, k] : Site 2) c =
        crossCount (jec_belowSet k) leftSide := by
    have hrightRay : jec_rayCount (![1, k] : Site 2) rightSide = 0 := by
      rw [jec_rayCount, List.countP_eq_zero]
      intro e he
      simp only [decide_eq_true_eq]
      intro hray
      induction e using Sym2.inductionOn with
      | _ u v =>
          have hu0 := hrSupport u
            (rightSide.fst_mem_support_of_mem_edges he)
          have hv0 := hrSupport v
            (rightSide.snd_mem_support_of_mem_edges he)
          have hfour := hrFour s(u, v) he
          rw [jec_rayEdge_mk] at hray
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hray
          rcases hray with ⟨⟨huv0, hcol⟩,
              ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩⟩
          · have huEq : u = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k hfour
          · have huEq : u = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k (by
                simpa [Sym2.eq_swap] using hfour)
    have hleftRay : jec_rayCount (![1, k] : Site 2) leftSide =
        crossCount (jec_belowSet k) leftSide := by
      apply jec_ray_eq_below
      intro z hz
      simpa using hlSupport z hz
    have hone : jec_rayCount (![1, k] : Site 2) c =
        crossCount (jec_belowSet k) leftSide := by
      dsimp only [c]
      rw [jec_rayCount_append, hrightRay, zero_add, hleftRay]
    have hzero : jec_rayCount (![0, k] : Site 2) c =
        jec_rayCount (![1, k] : Site 2) c := by
      rw [jec_rayCount, jec_rayCount]
      apply List.countP_congr
      intro e he
      simp only [decide_eq_true_eq]
      induction e using Sym2.inductionOn with
      | _ u v =>
          rw [jec_rayEdge_mk, jec_rayEdge_mk]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          constructor
          · rintro ⟨⟨huv0, hcol⟩, hrow⟩
            exact ⟨⟨huv0, by omega⟩, hrow⟩
          · rintro hright
            by_contra hleft
            have hcol : u 0 = 0 ∧ v 0 = 0 := by
              rcases hright with ⟨⟨huv0, hbound⟩, hrow⟩
              push Not at hleft
              have huNonneg : 0 ≤ u 0 := by omega
              exact ⟨by omega, by omega⟩
            rcases hright with ⟨⟨huv0, _hbound⟩,
                ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩⟩
            · have huEq : u = (![0, k - 1] : Site 2) := by
                ext i
                fin_cases i <;> simp <;> omega
              have hvEq : v = (![0, k] : Site 2) := by
                ext i
                fin_cases i <;> simp <;> omega
              exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
                gamma gamma' hfaith k (by
                  rw [← huEq, ← hvEq]
                  exact hcFour s(u, v) he)
            · have huEq : u = (![0, k] : Site 2) := by
                ext i
                fin_cases i <;> simp <;> omega
              have hvEq : v = (![0, k - 1] : Site 2) := by
                ext i
                fin_cases i <;> simp <;> omega
              exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
                gamma gamma' hfaith k (by
                  rw [← hvEq, ← huEq]
                  simpa [Sym2.eq_swap] using hcFour s(u, v) he)
    exact hzero.trans hone
  refine ⟨c, hcFour, ?_, ?_⟩
  · intro k hkLower hkUpper
    rw [ray_eq]
    intro heven
    have hsame := (crossCount_parity (jec_belowSet k) leftSide).mp heven
    have hupperNot : (gamma'.1.2.1 : Site 2) ∉ jec_belowSet k := by
      simp [jec_belowSet]
      omega
    have hlowerIn : (gamma.1.1 : Site 2) ∈ jec_belowSet k := by
      simp [jec_belowSet]
      omega
    exact hupperNot (hsame.mpr hlowerIn)
  · intro k hkOutside
    rw [ray_eq]
    apply (crossCount_parity (jec_belowSet k) leftSide).mpr
    simp [jec_belowSet]
    have horder := hfaith.axis_contacts_strict
    rcases hkOutside with hk | hk <;> omega


theorem rlc_axisInside_to_axisOutside_meets_connectorBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {kin kout : Int}
    (hinLower : (gamma.1.1 : Site 2) 1 < kin)
    (hinUpper : kin ≤ (gamma'.1.2.1 : Site 2) 1)
    (hout : kout ≤ (gamma.1.1 : Site 2) 1 ∨
      (gamma'.1.2.1 : Site 2) 1 < kout)
    (w : (hypercubicLattice 2).Walk
      (![0, kin] : Site 2) ![0, kout]) :
    ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
  obtain ⟨c, hcEdges, hcInside, hcOutside⟩ :=
    rlc_bookFourTraceAxisLoop_zeroRay_parity_of_faithful
      gamma gamma' hfaith
  have hcBarrier : ∀ z ∈ c.support,
      z ∈ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · simp [rlc_connectorBarrier, rlc_path_start_mem_vertices gamma.1]
    · exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' (hcEdges e he) hze
  obtain ⟨z, hzw, hzc⟩ :=
    ccs_closedLoop_separatingSide_forces_cross c
      {(![0, kin] : Site 2)} {(![0, kout] : Site 2)}
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hcInside kin hinLower hinUpper)
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hcOutside kout hout)
      (by simp) (by simp) w
  exact ⟨z, hzw, hcBarrier z hzc⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.boundaryPrefix_to_outsideAxis_meetsBarrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {N u v : Site 2} {k : Int}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk N u)
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨
      (gamma'.1.2.1 : Site 2) 1 < k) :
    ∃ (w : (hypercubicLattice 2).Walk
        (![0, L.boundary.height + 1] : Site 2) ![0, k]),
      (∀ z ∈ w.support,
        z = (![0, L.boundary.height + 1] : Site 2) ∨
          z = (![0, k] : Site 2) ∨
          ∃ f ∈ p.support, z = rlc_dualReflect f) ∧
      ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
  have huEq : rlc_dualReflect u = (![-1, k] : Site 2) := by
    rw [Sym2.eq_iff] at hreflected
    rcases hreflected with ⟨hu, _hv⟩ | ⟨hu, _hv⟩
    · exact hu
    · have h0 := congrArg (fun z : Site 2 => z 0) hu
      have h0' : (rlc_dualReflect u) 0 = 0 := by
        simpa only [Matrix.cons_val_zero] using h0
      omega
  have hstartAdj : (hypercubicLattice 2).Adj
      (![0, L.boundary.height + 1] : Site 2)
        ![-1, L.boundary.height + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hstartAdj' : (hypercubicLattice 2).Adj
      (![0, L.boundary.height + 1] : Site 2) (rlc_dualReflect N) := by
    rw [hN]
    exact hstartAdj
  let start : (hypercubicLattice 2).Walk
      (![0, L.boundary.height + 1] : Site 2) (rlc_dualReflect N) :=
    SimpleGraph.Walk.cons hstartAdj' SimpleGraph.Walk.nil
  let hle : faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) ≤
      hypercubicLattice 2 :=
    faceBoundaryGraph_le
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
  let reflected := (p.mapLe hle).map rlc_dualReflectLatticeHom
  have hendAdj : (hypercubicLattice 2).Adj
      (![-1, k] : Site 2) ![0, k] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hendAdj' : (hypercubicLattice 2).Adj
      (rlc_dualReflect u) (![0, k] : Site 2) := by
    rw [huEq]
    exact hendAdj
  let finish : (hypercubicLattice 2).Walk
      (rlc_dualReflect u) (![0, k] : Site 2) :=
    SimpleGraph.Walk.cons hendAdj' SimpleGraph.Walk.nil
  let w := start.append (reflected.append finish)
  have hwSupport : ∀ z ∈ w.support,
      z = (![0, L.boundary.height + 1] : Site 2) ∨
        z = (![0, k] : Site 2) ∨
        ∃ f ∈ p.support, z = rlc_dualReflect f := by
    intro z hz
    dsimp only [w] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hzStart | hzRest
    · dsimp only [start] at hzStart
      change z ∈ ((![0, L.boundary.height + 1] : Site 2) ::
        [rlc_dualReflect N]) at hzStart
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzStart
      rcases hzStart with hzAxis | hzN
      · exact Or.inl hzAxis
      · exact Or.inr (Or.inr ⟨N, p.start_mem_support, hzN⟩)
    · have hzRest' :=
        (SimpleGraph.Walk.mem_support_append_iff reflected finish).mp hzRest
      rcases hzRest' with hzReflected | hzFinish
      dsimp only [reflected] at hzReflected
      rw [SimpleGraph.Walk.support_map, List.mem_map,
        SimpleGraph.Walk.support_mapLe_eq_support] at hzReflected
      obtain ⟨f, hf, rfl⟩ := hzReflected
      exact Or.inr (Or.inr ⟨f, hf, rfl⟩)
      dsimp only [finish] at hzFinish
      change z ∈ (rlc_dualReflect u :: [(![0, k] : Site 2)]) at hzFinish
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzFinish
      rcases hzFinish with hzU | hzAxis
      · exact Or.inr (Or.inr ⟨u, p.end_mem_support, hzU⟩)
      · exact Or.inr (Or.inl hzAxis)
  have hkLower : (gamma.1.1 : Site 2) 1 <
      L.boundary.height + 1 := by
    have := L.boundary.height_lower
    omega
  have hkUpper : L.boundary.height + 1 ≤
      (gamma'.1.2.1 : Site 2) 1 := by
    have := L.boundary.height_upper
    omega
  exact ⟨w, hwSupport,
    rlc_axisInside_to_axisOutside_meets_connectorBarrier
      gamma gamma' hfaith hkLower hkUpper hkOutside w⟩


theorem rlc_connectorBarrier_mem_connectorBox {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorBarrier gamma gamma') :
    z ∈ rect (-2 * n) (2 * n) (-n) n := by
  simp only [rlc_connectorBarrier, Finset.mem_union] at hz
  rcases hz with ((hright | hleft) | hflipRight) | hflipLeft
  · exact rlc_rightPathVertex_mem_connectorBox gamma hright
  · exact rlc_leftPathVertex_mem_connectorBox gamma' hleft
  · obtain ⟨z0, hz0, rfl⟩ := Finset.mem_image.mp hflipRight
    exact (rlc_mem_connectorBox_flipX z0).mp
      (rlc_rightPathVertex_mem_connectorBox gamma hz0)
  · obtain ⟨z0, hz0, rfl⟩ := Finset.mem_image.mp hflipLeft
    exact (rlc_mem_connectorBox_flipX z0).mp
      (rlc_leftPathVertex_mem_connectorBox gamma' hz0)


theorem rlc_connectorBoxBoundary_detour_avoidsBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {k : Int} {z : Site 2}
    (hzBoundary : z 0 = -2 * n ∨ z 0 = 2 * n ∨
      z 1 = -n ∨ z 1 = n)
    (hzNot : z ∉ rlc_connectorBarrier gamma gamma') :
    ∃ p : (hypercubicLattice 2).Walk z (![2 * n + 1, k] : Site 2),
      ∀ w ∈ p.support, w ∉ rlc_connectorBarrier gamma gamma' := by
  have hzCoord : z = (![z 0, z 1] : Site 2) := by
    ext i
    fin_cases i <;> simp
  have houtside {w : Site 2}
      (hw : w ∉ rect (-2 * n) (2 * n) (-n) n) :
      w ∉ rlc_connectorBarrier gamma gamma' := by
    intro hwBarrier
    exact hw (rlc_connectorBarrier_mem_connectorBox gamma gamma' hwBarrier)
  rcases hzBoundary with hzLeft | hzRight | hzBottom | hzTop
  · let first : (hypercubicLattice 2).Walk z
        (![-2 * n - 1, z 1] : Site 2) :=
      (sw_horizSeg (z 1) (z 0) (-2 * n - 1)).copy hzCoord.symm rfl
    let second : (hypercubicLattice 2).Walk
        (![-2 * n - 1, z 1] : Site 2)
        (![-2 * n - 1, n + 1] : Site 2) :=
      sw_vertSeg (-2 * n - 1) (z 1) (n + 1)
    let third := sw_lshape (-2 * n - 1) (n + 1) (2 * n + 1) k
    let p := (first.append second).append third
    refine ⟨p, ?_⟩
    intro w hw
    dsimp only [p] at hw
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with (hw | hw) | hw
    · dsimp only [first] at hw
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      rw [Set.mem_uIcc] at ht
      by_cases htEq : t = -2 * n
      · have : (![t, z 1] : Site 2) = z := by
          rw [htEq, ← hzLeft]
          exact hzCoord.symm
        rwa [this]
      · apply houtside
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
    · dsimp only [second] at hw
      rw [sw_vertSeg_mem_support] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      apply houtside
      simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · change w ∈
        (sw_lshape (-2 * n - 1) (n + 1) (2 * n + 1) k).support at hw
      rw [sw_lshape_support_eq] at hw
      rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
        apply houtside <;>
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        omega
  · let p :=
      (sw_lshape (z 0) (z 1) (2 * n + 1) k).copy hzCoord.symm rfl
    refine ⟨p, ?_⟩
    intro w hw
    dsimp only [p] at hw
    rw [SimpleGraph.Walk.support_copy, sw_lshape_support_eq] at hw
    rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [Set.mem_uIcc] at ht
      by_cases htEq : t = 2 * n
      · have : (![t, z 1] : Site 2) = z := by
          rw [htEq, ← hzRight]
          exact hzCoord.symm
        rwa [this]
      · apply houtside
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
    · apply houtside
      simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · let first : (hypercubicLattice 2).Walk z
        (![z 0, -n - 1] : Site 2) :=
      (sw_vertSeg (z 0) (z 1) (-n - 1)).copy hzCoord.symm rfl
    let second := sw_lshape (z 0) (-n - 1) (2 * n + 1) k
    let p := first.append second
    refine ⟨p, ?_⟩
    intro w hw
    dsimp only [p] at hw
    rw [SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw
    · dsimp only [first] at hw
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      rw [Set.mem_uIcc] at ht
      by_cases htEq : t = -n
      · have : (![z 0, t] : Site 2) = z := by
          rw [htEq, ← hzBottom]
          exact hzCoord.symm
        rwa [this]
      · apply houtside
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
    · change w ∈ (sw_lshape (z 0) (-n - 1) (2 * n + 1) k).support at hw
      rw [sw_lshape_support_eq] at hw
      rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
        apply houtside <;>
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        omega
  · let first : (hypercubicLattice 2).Walk z
        (![z 0, n + 1] : Site 2) :=
      (sw_vertSeg (z 0) (z 1) (n + 1)).copy hzCoord.symm rfl
    let second := sw_lshape (z 0) (n + 1) (2 * n + 1) k
    let p := first.append second
    refine ⟨p, ?_⟩
    intro w hw
    dsimp only [p] at hw
    rw [SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw
    · dsimp only [first] at hw
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      rw [Set.mem_uIcc] at ht
      by_cases htEq : t = n
      · have : (![z 0, t] : Site 2) = z := by
          rw [htEq, ← hzTop]
          exact hzCoord.symm
        rwa [this]
      · apply houtside
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
    · change w ∈ (sw_lshape (z 0) (n + 1) (2 * n + 1) k).support at hw
      rw [sw_lshape_support_eq] at hw
      rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
        apply houtside <;>
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        omega


theorem rlc_axisGap_to_rightExterior_meets_connectorBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {k : Int}
    (hkLower : (gamma.1.1 : Site 2) 1 < k)
    (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1)
    (w : (hypercubicLattice 2).Walk
      (![1, k] : Site 2) (![2 * n + 1, k] : Site 2)) :
    ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
  obtain ⟨c, _hS, _hU, hcEdges, hcOdd⟩ :=
    rlc_bookFourTraceAxisLoop_of_faithful gamma gamma' hfaith
  have hcBarrier : ∀ z ∈ c.support,
      z ∈ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · simp [rlc_connectorBarrier, rlc_path_start_mem_vertices gamma.1]
    · exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' (hcEdges e he) hze
  have hfar : ∀ z ∈ c.support, z 0 ≤
      (![2 * n + 1, k] : Site 2) 0 - 1 := by
    intro z hz
    have hzBox := rlc_connectorBarrier_mem_connectorBox
      gamma gamma' (hcBarrier z hz)
    rw [mem_rect] at hzBox
    simpa using hzBox.2.1
  have hodd := hcOdd k hkLower hkUpper
  have heven := jec_ray_even_far c (![2 * n + 1, k] : Site 2) hfar
  obtain ⟨z, hzw, hzc⟩ :=
    ccs_closedLoop_separatingSide_forces_cross c
      {(![1, k] : Site 2)} {(![2 * n + 1, k] : Site 2)}
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hodd)
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact heven)
      (by simp) (by simp) w
  exact ⟨z, hzw, hcBarrier z hzc⟩


theorem rlc_axisGapAxis_to_rightExterior_meets_connectorBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {k : Int}
    (hkLower : (gamma.1.1 : Site 2) 1 < k)
    (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1)
    (w : (hypercubicLattice 2).Walk
      (![0, k] : Site 2) (![2 * n + 1, k] : Site 2)) :
    ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
  obtain ⟨c, hcEdges, hcOdd⟩ :=
    rlc_bookFourTraceAxisLoop_zeroRay_odd_of_faithful
      gamma gamma' hfaith
  have hcBarrier : ∀ z ∈ c.support,
      z ∈ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · simp [rlc_connectorBarrier, rlc_path_start_mem_vertices gamma.1]
    · exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' (hcEdges e he) hze
  have hfar : ∀ z ∈ c.support, z 0 ≤
      (![2 * n + 1, k] : Site 2) 0 - 1 := by
    intro z hz
    have hzBox := rlc_connectorBarrier_mem_connectorBox
      gamma gamma' (hcBarrier z hz)
    rw [mem_rect] at hzBox
    simpa using hzBox.2.1
  have hodd := hcOdd k hkLower hkUpper
  have heven := jec_ray_even_far c (![2 * n + 1, k] : Site 2) hfar
  obtain ⟨z, hzw, hzc⟩ :=
    ccs_closedLoop_separatingSide_forces_cross c
      {(![0, k] : Site 2)} {(![2 * n + 1, k] : Site 2)}
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hodd)
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact heven)
      (by simp) (by simp) w
  exact ⟨z, hzw, hcBarrier z hzc⟩


end
end StatMech.Universality
