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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part26
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_twoChannelFullPhysicalLiftFace_of_mem {n : Int}
    (gamma : RlcRightDiagonalPath n) (f : Site 2)
    (hf : rlc_dualReflect f ∈ rect (-2 * n) (2 * n) (-n) n) :
    rlc_twoChannelFullPhysicalLiftFace gamma f =
      ⟨rlc_dualReflect f, hf⟩ := by
  classical
  unfold rlc_twoChannelFullPhysicalLiftFace
  split
  · rfl
  · rename_i hnot
    exact (hnot hf).elim


theorem rlc_twoChannelFullPhysical_goodBoundary_le_staticCutTarget
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
    ∀ {f g : Site 2},
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig
            gamma gamma' A)).Adj f g →
        (rlc_twoChannelFullPhysicalCutTargetGraphAt
          gamma gamma' A).Adj
            (rlc_twoChannelFullPhysicalLiftFace gamma f)
            (rlc_twoChannelFullPhysicalLiftFace gamma g) := by
  intro f g hfg
  have hcarrier : RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' f g :=
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).mp
          hfg |>.2
  obtain ⟨hf, hg, _hfgTarget⟩ :=
    (rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local
      gamma gamma' f g).mp
        ((rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
          gamma gamma' f g).mp hcarrier).1
  obtain ⟨target, htarget, u, v, hsource, hcross⟩ :=
    rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut
      gamma gamma' A hAright hAleft hfg.1 hcarrier
  refine ⟨target, ?_, u, v, hsource, hcross⟩
  apply Sym2.map.injective Subtype.val_injective
  simpa [rlc_twoChannelFullPhysicalLiftFace_of_mem gamma f hf,
    rlc_twoChannelFullPhysicalLiftFace_of_mem gamma g hg,
    Sym2.map_mk] using htarget


theorem
    rlc_twoChannelFullPhysical_goodBoundary_ne_reachableSourceCrossing_atCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {f g p q : Site 2}
    (hfg : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Adj f g)
    (hp : p ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hq : q ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hcross : sharedPrimalEdge f g = s(p, q)) : False := by
  have hcarrier : RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' f g :=
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).mp
          hfg |>.2
  obtain ⟨target, htarget, hsourceCross⟩ :=
    rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut
      gamma gamma' A hAright hAleft hfg.1 hcarrier
  obtain ⟨u, v, hsource, huv⟩ := hsourceCross
  have hsourceMap :
      (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val =
        sharedPrimalEdge f g := by
    calc
      (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val =
          rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) :=
        rlc_twoChannelFullPhysicalSourceEdge_map target
      _ = rlc_pimsEdgeEquiv
          s(rlc_dualReflect f, rlc_dualReflect g) := by rw [htarget]
      _ = sharedPrimalEdge f g :=
        rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg.1.1
  have huvSite : s(u.1, v.1) = s(p, q) := by
    calc
      s(u.1, v.1) =
          (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val := by
        rw [hsource, Sym2.map_mk]
      _ = sharedPrimalEdge f g := hsourceMap
      _ = s(p, q) := hcross
  have hpCut := rlc_twoChannelFullReachSet_subset_staticCut
    gamma gamma' A hAright hAleft hp
  have hqCut := rlc_twoChannelFullReachSet_subset_staticCut
    gamma gamma' A hAright hAleft hq
  rw [Sym2.eq_iff] at huvSite
  rcases huvSite with ⟨hup, hvq⟩ | ⟨huq, hvp⟩
  · have huA : u ∈ A :=
      (rlc_twoChannelFullPhysicalLiftVertexCut_mem A u).mp
        (by simpa [hup] using hpCut)
    have hvA : v ∈ A :=
      (rlc_twoChannelFullPhysicalLiftVertexCut_mem A v).mp
        (by simpa [hvq] using hqCut)
    rcases huv with ⟨_, hvNot⟩ | ⟨_, huNot⟩
    · exact hvNot hvA
    · exact huNot huA
  · have huA : u ∈ A :=
      (rlc_twoChannelFullPhysicalLiftVertexCut_mem A u).mp
        (by simpa [huq] using hqCut)
    have hvA : v ∈ A :=
      (rlc_twoChannelFullPhysicalLiftVertexCut_mem A v).mp
        (by simpa [hvp] using hpCut)
    rcases huv with ⟨_, hvNot⟩ | ⟨_, huNot⟩
    · exact hvNot hvA
    · exact huNot huA


theorem
    rlc_twoChannelFullPhysical_reachableSource_goodBoundary_subdiv_disjoint_atCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {a b f g : Site 2}
    (H : (hypercubicLattice 2).Walk a b)
    (hHReach : ∀ v ∈ H.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (V : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk f g) :
    ¬∃ z : Site 2,
      z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support ∧
        z ∈ (StatMech.TwoDim.zfe_faceSubdiv
          ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))).mapLe
            (faceBoundaryGraph_le
              (rlc_twoChannelFullFilledReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A))))).support := by
  rintro ⟨z, hzH, hzV⟩
  let Vface : (hypercubicLattice 2).Walk f g :=
    (V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).mapLe
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))
  have hzVface : z ∈ (StatMech.TwoDim.zfe_faceSubdiv Vface).support := by
    exact hzV
  obtain ⟨p, q, f', g', hpq, hfg, hshared⟩ :=
    StatMech.TwoDim.zfe_subdiv_meeting_edge H Vface hzH hzVface
  have hfgGood : s(f', g') ∈ V.edges := by
    simpa [Vface, SimpleGraph.Walk.edges_mapLe_eq_edges] using hfg
  exact
    rlc_twoChannelFullPhysical_goodBoundary_ne_reachableSourceCrossing_atCut
      gamma gamma' A hAright hAleft (V.adj_of_mem_edges hfgGood)
        (hHReach p (H.fst_mem_support_of_mem_edges hpq))
        (hHReach q (H.snd_mem_support_of_mem_edges hpq)) hshared.symm


theorem rlc_zfe_primalSubdiv_mem_doubledRect
    {a b : Site 2} (H : (hypercubicLattice 2).Walk a b)
    (left right bottom top : Int)
    (hH : ∀ z ∈ H.support, z ∈ rect left right bottom top) :
    ∀ z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support,
      z ∈ rect (2 * left) (2 * right) (2 * bottom) (2 * top) := by
  intro z hz
  rcases StatMech.TwoDim.zfe_primalSubdiv_support_cases H hz with
      ⟨p, hp, rfl⟩ | ⟨p, q, hpq, rfl⟩
  · have hpBox := hH p hp
    simp only [StatMech.TwoDim.zfe_primalEmb, mem_rect,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hpBox ⊢
    omega
  · have hpBox := hH p (H.fst_mem_support_of_mem_edges hpq)
    have hqBox := hH q (H.snd_mem_support_of_mem_edges hpq)
    simp only [StatMech.TwoDim.zfe_primalMid, mem_rect,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hpBox hqBox ⊢
    omega


theorem rlc_zfe_faceSubdiv_mem_doubledRect
    {f g : Site 2} (V : (hypercubicLattice 2).Walk f g)
    (left right bottom top : Int)
    (hV : ∀ z ∈ V.support, z ∈ rect left right bottom top) :
    ∀ z ∈ (StatMech.TwoDim.zfe_faceSubdiv V).support,
      z ∈ rect (2 * left + 1) (2 * right + 1)
        (2 * bottom + 1) (2 * top + 1) := by
  intro z hz
  rcases StatMech.TwoDim.zfe_faceSubdiv_support_cases V hz with
      ⟨p, hp, rfl⟩ | ⟨p, q, hpq, rfl⟩
  · have hpBox := hV p hp
    simp only [StatMech.TwoDim.zfe_faceEmb, mem_rect,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hpBox ⊢
    omega
  · have hpBox := hV p (V.fst_mem_support_of_mem_edges hpq)
    have hqBox := hV q (V.snd_mem_support_of_mem_edges hpq)
    simp only [StatMech.TwoDim.zfe_faceMid, mem_rect,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hpBox hqBox ⊢
    omega


theorem
    rlc_twoChannelFullPhysical_not_reachableSource_goodBoundary_transverse_atCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {a b f g : Site 2}
    (H : (hypercubicLattice 2).Walk a b)
    (hHReach : ∀ v ∈ H.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (V : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk f g)
    (alpha beta bottom top : Int)
    (hab : alpha < beta) (hbt : bottom ≤ top)
    (hHstartBox : StatMech.TwoDim.zfe_primalEmb a ∈
      rect alpha beta bottom top)
    (hHendBox : StatMech.TwoDim.zfe_primalEmb b ∈
      rect alpha beta bottom top)
    (hHstartLeft : StatMech.TwoDim.zfe_primalEmb a 0 = alpha)
    (hHendRight : StatMech.TwoDim.zfe_primalEmb b 0 = beta)
    (hHBox : ∀ z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support,
      z ∈ rect alpha beta bottom top)
    (hVstartBottom : StatMech.TwoDim.zfe_faceEmb f 1 = bottom)
    (hVendTop : StatMech.TwoDim.zfe_faceEmb g 1 = top)
    (hVstartX : alpha ≤ StatMech.TwoDim.zfe_faceEmb f 0 ∧
      StatMech.TwoDim.zfe_faceEmb f 0 ≤ beta)
    (hVendX : alpha ≤ StatMech.TwoDim.zfe_faceEmb g 0 ∧
      StatMech.TwoDim.zfe_faceEmb g 0 ≤ beta)
    (hVBox : ∀ z ∈
      (StatMech.TwoDim.zfe_faceSubdiv
        ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A))).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))).support,
      z ∈ rect alpha beta bottom top) : False := by
  let Vface : (hypercubicLattice 2).Walk f g :=
    (V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).mapLe
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))
  let Vd := StatMech.TwoDim.zfe_faceSubdiv Vface
  have hfEndpoint : StatMech.TwoDim.zfe_faceEmb f =
      ![StatMech.TwoDim.zfe_faceEmb f 0, bottom] := by
    ext i
    fin_cases i
    · rfl
    · simpa using hVstartBottom
  have hgEndpoint : StatMech.TwoDim.zfe_faceEmb g =
      ![StatMech.TwoDim.zfe_faceEmb g 0, top] := by
    ext i
    fin_cases i
    · rfl
    · simpa using hVendTop
  let Vdc : (hypercubicLattice 2).Walk
      ![StatMech.TwoDim.zfe_faceEmb f 0, bottom]
      ![StatMech.TwoDim.zfe_faceEmb g 0, top] :=
    Vd.copy hfEndpoint hgEndpoint
  have hVdcBox : ∀ z ∈ Vdc.support,
      z ∈ rect alpha beta bottom top := by
    intro z hz
    apply hVBox z
    simpa [Vdc, Vd, Vface, SimpleGraph.Walk.support_copy] using hz
  have hsep : Lattice.ArcSeparatingSet
      {z : Site 2 | z ∈ Vdc.support} alpha beta bottom top :=
    Lattice.jec_arcSeparatingSet alpha beta bottom top
      (StatMech.TwoDim.zfe_faceEmb f 0)
      (StatMech.TwoDim.zfe_faceEmb g 0) hab hbt
      hVstartX.1 hVstartX.2 hVendX.1 hVendX.2 Vdc hVdcBox
      {z : Site 2 | z ∈ Vdc.support} (by intro z hz; exact hz)
  obtain ⟨z, hzH, hzVdc⟩ :=
    Lattice.tpc_two_paths_cross_of_sep hsep
      hHstartBox hHendBox hHstartLeft hHendRight
      (StatMech.TwoDim.zfe_primalSubdiv H) hHBox
  have hzV : z ∈ (StatMech.TwoDim.zfe_faceSubdiv Vface).support := by
    simpa [Vdc, Vd, SimpleGraph.Walk.support_copy] using hzVdc
  exact
    rlc_twoChannelFullPhysical_reachableSource_goodBoundary_subdiv_disjoint_atCut
      gamma gamma' A hAright hAleft H hHReach V ⟨z, hzH, by
        simpa [Vface] using hzV⟩


theorem
    rlc_twoChannelFullPhysical_not_reachableSource_goodBoundary_collared_atCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {a b f g : Site 2}
    (H : (hypercubicLattice 2).Walk a b)
    (hHReach : ∀ v ∈ H.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (V : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk f g)
    (alpha beta bottom top : Int)
    (hab : alpha < beta) (hbt : bottom ≤ top)
    (hHBox : ∀ z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support,
      z ∈ rect alpha beta bottom top)
    (hVBox : ∀ z ∈
      (StatMech.TwoDim.zfe_faceSubdiv
        ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A))).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))).support,
      z ∈ rect alpha beta bottom top)
    (hLower : ∀ z ∈
      (Lattice.horizontalWallExtension alpha beta
        (StatMech.TwoDim.zfe_primalSubdiv H)).support,
      z ∈ (sw_vertSeg (StatMech.TwoDim.zfe_faceEmb f 0)
        bottom (StatMech.TwoDim.zfe_faceEmb f 1)).support →
      z ∈ (StatMech.TwoDim.zfe_faceSubdiv
        ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A))).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))).support)
    (hUpper : ∀ z ∈
      (Lattice.horizontalWallExtension alpha beta
        (StatMech.TwoDim.zfe_primalSubdiv H)).support,
      z ∈ (sw_vertSeg (StatMech.TwoDim.zfe_faceEmb g 0)
        (StatMech.TwoDim.zfe_faceEmb g 1) top).support →
      z ∈ (StatMech.TwoDim.zfe_faceSubdiv
        ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A))).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))).support)
    (hLeft : ∀ z ∈
      (StatMech.TwoDim.zfe_faceSubdiv
        ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A))).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))).support,
      z ∈ (sw_horizSeg (StatMech.TwoDim.zfe_primalEmb a 1)
        alpha (StatMech.TwoDim.zfe_primalEmb a 0)).support →
      z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support)
    (hRight : ∀ z ∈
      (StatMech.TwoDim.zfe_faceSubdiv
        ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A))).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))).support,
      z ∈ (sw_horizSeg (StatMech.TwoDim.zfe_primalEmb b 1)
        (StatMech.TwoDim.zfe_primalEmb b 0) beta).support →
      z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support) : False := by
  let Vface : (hypercubicLattice 2).Walk f g :=
    (V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).mapLe
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))
  let Hd := StatMech.TwoDim.zfe_primalSubdiv H
  let Vd := StatMech.TwoDim.zfe_faceSubdiv Vface
  have haBox : StatMech.TwoDim.zfe_primalEmb a ∈
      rect alpha beta bottom top := hHBox _ Hd.start_mem_support
  have hbBox : StatMech.TwoDim.zfe_primalEmb b ∈
      rect alpha beta bottom top := hHBox _ Hd.end_mem_support
  have hfBox : StatMech.TwoDim.zfe_faceEmb f ∈
      rect alpha beta bottom top := by
    apply hVBox
    exact Vd.start_mem_support
  have hgBox : StatMech.TwoDim.zfe_faceEmb g ∈
      rect alpha beta bottom top := by
    apply hVBox
    exact Vd.end_mem_support
  obtain ⟨z, hzH, hzV⟩ := Lattice.collaredWalks_meet_on_original_supports
    hab hbt Vd Hd hfBox hgBox haBox hbBox hVBox hHBox
      hLower hUpper hLeft hRight
  exact
    rlc_twoChannelFullPhysical_reachableSource_goodBoundary_subdiv_disjoint_atCut
      gamma gamma' A hAright hAleft H hHReach V ⟨z, hzH, by
        simpa [Vd, Vface] using hzV⟩


theorem rlc_twoChannelFullPhysical_goodBoundary_reachable_staticCutTarget
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {f g : Site 2}
    (hfg : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Reachable
        f g) :
    (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable
      (rlc_twoChannelFullPhysicalLiftFace gamma f)
      (rlc_twoChannelFullPhysicalLiftFace gamma g) := by
  let hom :
      rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) →g
        rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A :=
    { toFun := rlc_twoChannelFullPhysicalLiftFace gamma
      map_rel' := by
        intro x y hxy
        exact rlc_twoChannelFullPhysical_goodBoundary_le_staticCutTarget
          gamma gamma' A hAright hAleft hxy }
  exact hfg.map hom


theorem
    rlc_twoChannelFullPhysical_staticCutTargetConnector_of_goodComponent
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hgood : RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) :
    ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧
        rlc_connectorOnLeft gamma' y ∧
          (rlc_twoChannelFullPhysicalCutTargetGraphAt
            gamma gamma' A).Reachable x y := by
  obtain ⟨f, g, hfg, hfPath, hgPath⟩ := hgood
  have hfBox : rlc_dualReflect f ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_rightPathVertex_mem_connectorBox gamma hfPath
  have hgBox : rlc_dualReflect g ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_leftPathVertex_mem_connectorBox gamma' hgPath
  let x : RlcConnectorVertex n := ⟨rlc_dualReflect f, hfBox⟩
  let y : RlcConnectorVertex n := ⟨rlc_dualReflect g, hgBox⟩
  refine ⟨x, y, ?_, ?_, ?_⟩
  · exact hfPath
  · exact hgPath
  · have hreach :=
      rlc_twoChannelFullPhysical_goodBoundary_reachable_staticCutTarget
        gamma gamma' A hAright hAleft hfg
    simpa [x, y, rlc_twoChannelFullPhysicalLiftFace_of_mem gamma f hfBox,
      rlc_twoChannelFullPhysicalLiftFace_of_mem gamma g hgBox] using hreach


theorem rlc_twoChannelFullPhysical_staticCutFailure_separates_traceComponents
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hfailure : ¬∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧
        rlc_connectorOnLeft gamma' y ∧
          (rlc_twoChannelFullPhysicalCutTargetGraphAt
            gamma gamma' A).Reachable x y)
    {x y a b : RlcConnectorVertex n}
    (hx : rlc_connectorOnRight gamma x)
    (hy : rlc_connectorOnLeft gamma' y)
    (hxa : (rlc_twoChannelFullPhysicalCutTargetGraphAt
      gamma gamma' A).Reachable x a)
    (hyb : (rlc_twoChannelFullPhysicalCutTargetGraphAt
      gamma gamma' A).Reachable y b) :
    ¬(rlc_twoChannelFullPhysicalCutTargetGraphAt
      gamma gamma' A).Reachable a b := by
  intro hab
  apply hfailure
  exact ⟨x, y, hx, hy, hxa.trans (hab.trans hyb.symm)⟩


theorem RlcBookFaithfulTracePair.scale_pos {n : Int}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') : 0 < n := by
  have hbox := gamma.1.1.2.1
  rw [mem_rect] at hbox
  have hstrict := hfaith.right_axis_strict
  omega


theorem RlcBookFaithfulTracePair.origin_mem_connectorAllowed {n : Int}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    origin 2 ∈ rlc_connectorAllowed gamma gamma' := by
  have hn : 0 < n := hfaith.scale_pos
  have hnotRight : origin 2 ∉ rlc_pathVertices gamma.1 := by
    intro hmem
    have haxis : (origin 2) 0 = 0 := by simp [origin]
    have heq := hfaith.right_axis_unique hmem haxis
    have hheight := congrArg (fun z : Site 2 => z 1) heq
    have hstrict := hfaith.right_axis_strict
    simp [origin] at hheight
    omega
  have hnotLeft : origin 2 ∉ rlc_pathVertices gamma'.1 := by
    intro hmem
    have haxis : (origin 2) 0 = 0 := by simp [origin]
    have heq := hfaith.left_axis_unique hmem haxis
    have hheight := congrArg (fun z : Site 2 => z 1) heq
    have hstrict := hfaith.left_axis_strict
    simp [origin] at hheight
    omega
  rw [rlc_connectorAllowed, Finset.mem_sdiff]
  constructor
  · simp [rlc_connectorBox, mem_rect, origin, le_of_lt hn]
  · intro hbarrier
    have horigin : origin 2 = (![0, 0] : Site 2) := by
      ext i
      fin_cases i <;> rfl
    rw [horigin, rlc_axis_mem_connectorBarrier_iff gamma gamma' 0]
      at hbarrier
    rw [← horigin] at hbarrier
    exact hbarrier.elim hnotRight hnotLeft


theorem RlcBookFaithfulTracePair.origin_mem_connectorOriginRegion {n : Int}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    origin 2 ∈ rlc_connectorOriginRegion gamma gamma' := by
  rw [rlc_connectorOriginRegion]
  simp only [Set.Finite.mem_toFinset]
  let ho : origin 2 ∈ rlc_connectorAllowed gamma gamma' :=
    hfaith.origin_mem_connectorAllowed
  exact ⟨ho, ho, SimpleGraph.Reachable.refl _⟩


theorem RlcBookFaithfulTracePair.axisGap_mem_connectorOriginRegion {n : Int}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (t : Int)
    (hbelow : (gamma.1.1 : Site 2) 1 < t)
    (habove : t < (gamma'.1.2.1 : Site 2) 1) :
    (![0, t] : Site 2) ∈ rlc_connectorOriginRegion gamma gamma' := by
  let z : Site 2 := ![0, t]
  let w : (hypercubicLattice 2).Walk (origin 2) z :=
    (sw_vertSeg 0 0 t).copy
      (by ext i; fin_cases i <;> rfl)
      (by ext i; fin_cases i <;> rfl)
  have hrightNeg : (gamma.1.1 : Site 2) 1 < 0 :=
    hfaith.right_axis_strict
  have hleftPos : 0 < (gamma'.1.2.1 : Site 2) 1 :=
    hfaith.left_axis_strict
  have hsupp : ∀ v ∈ w.support,
      v ∈ rlc_connectorAllowed gamma gamma' := by
    intro v hv
    have hv0 : v 0 = 0 := by
      have hv' : v ∈ (sw_vertSeg 0 0 t).support := by
        simpa [w, SimpleGraph.Walk.support_copy] using hv
      rw [sw_vertSeg_mem_support] at hv'
      obtain ⟨k, _hk, rfl⟩ := hv'
      simp
    have hvI : v 1 ∈ Set.uIcc 0 t := by
      have hv' : v ∈ (sw_vertSeg 0 0 t).support := by
        simpa [w, SimpleGraph.Walk.support_copy] using hv
      rw [sw_vertSeg_mem_support] at hv'
      obtain ⟨k, hk, hkv⟩ := hv'
      have hv1 : v 1 = k := by rw [hkv]; simp
      simpa [hv1] using hk
    have hvBounds : (gamma.1.1 : Site 2) 1 < v 1 ∧
        v 1 < (gamma'.1.2.1 : Site 2) 1 := by
      rw [Set.mem_uIcc] at hvI
      rcases hvI with hvI | hvI <;> omega
    rw [rlc_connectorAllowed, Finset.mem_sdiff]
    constructor
    · simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
      rw [mem_rect]
      have hrightBox := gamma.1.1.2.1
      have hleftBox := gamma'.1.2.1.2.1
      rw [mem_rect] at hrightBox hleftBox
      constructor
      · simp [hv0]
        exact le_of_lt hfaith.scale_pos
      · omega
    · have hvSite : v = (![0, v 1] : Site 2) := by
        ext i
        fin_cases i <;> simp [hv0]
      rw [hvSite, rlc_axis_mem_connectorBarrier_iff gamma gamma' (v 1)]
      push Not
      constructor
      · intro hvRight
        have heq := hfaith.right_axis_unique hvRight (by simp)
        have hheight : v 1 = (gamma.1.1 : Site 2) 1 := by
          simpa using congrArg (fun u : Site 2 => u 1) heq
        omega
      · intro hvLeft
        have heq := hfaith.left_axis_unique hvLeft (by simp)
        have hheight : v 1 = (gamma'.1.2.1 : Site 2) 1 := by
          simpa using congrArg (fun u : Site 2 => u 1) heq
        omega
  have hw := w.induce
    (rlc_connectorAllowed gamma gamma' : Set (Site 2)) hsupp
  rw [rlc_connectorOriginRegion]
  simp only [Set.Finite.mem_toFinset]
  let hz : z ∈ rlc_connectorAllowed gamma gamma' :=
    hsupp z w.end_mem_support
  let ho : origin 2 ∈ rlc_connectorAllowed gamma gamma' :=
    hsupp (origin 2) w.start_mem_support
  refine ⟨hz, ho, ?_⟩
  have hreach := hw.reachable
  simpa only [z] using hreach


theorem rlc_bookFaithful_axisGapVertical_mem_connectorEdges {n : Int}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (t : Int)
    (hbelow : (gamma.1.1 : Site 2) 1 < t)
    (habove : t + 1 < (gamma'.1.2.1 : Site 2) 1) :
    s((![0, t] : Site 2), ![0, t + 1]) ∈
      rlc_connectorEdges gamma gamma' := by
  have htRegion := hfaith.axisGap_mem_connectorOriginRegion
    t hbelow (by omega)
  have ht1Region := hfaith.axisGap_mem_connectorOriginRegion
    (t + 1) (by omega) (by omega)
  have htBox : (![0, t] : Site 2) ∈ rlc_connectorBox n := by
    have htSet : (![0, t] : Site 2) ∈
        rlc_connectorOriginRegionSet gamma gamma' := by
      simpa [rlc_connectorOriginRegion] using htRegion
    exact (Finset.mem_sdiff.mp htSet.1).1
  have ht1Box : (![0, t + 1] : Site 2) ∈ rlc_connectorBox n := by
    have ht1Set : (![0, t + 1] : Site 2) ∈
        rlc_connectorOriginRegionSet gamma gamma' := by
      simpa [rlc_connectorOriginRegion] using ht1Region
    exact (Finset.mem_sdiff.mp ht1Set.1).1
  rw [rlc_connectorEdges, Finset.mem_filter]
  exact ⟨by
    rw [mem_edgesWithinFinset]
    exact ⟨![0, t], htBox, ![0, t + 1], ht1Box, rfl⟩,
    ⟨![0, t], htRegion, Sym2.mem_mk_left _ _⟩⟩


theorem rlc_bookFaithful_axisGapVertical_preimage_mem_connectorEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (t : Int)
    (hbelow : (gamma.1.1 : Site 2) 1 < t)
    (habove : t < (gamma'.1.2.1 : Site 2) 1) :
    rlc_pimsEdgeEquiv s((![0, t] : Site 2), ![0, t + 1]) ∈
      rlc_connectorEdges gamma gamma' := by
  rw [show rlc_pimsEdgeEquiv s((![0, t] : Site 2), ![0, t + 1]) =
      s((![-1, t] : Site 2), ![0, t]) by
    simpa using rlc_pimsEdgeEquiv_vertical 0 t]
  have htRegion := hfaith.axisGap_mem_connectorOriginRegion
    t hbelow habove
  have htBox : (![0, t] : Site 2) ∈ rlc_connectorBox n := by
    have htSet : (![0, t] : Site 2) ∈
        rlc_connectorOriginRegionSet gamma gamma' := by
      simpa [rlc_connectorOriginRegion] using htRegion
    exact (Finset.mem_sdiff.mp htSet.1).1
  have hleftBox : (![-1, t] : Site 2) ∈ rlc_connectorBox n := by
    have htSet : (![0, t] : Site 2) ∈
        rlc_connectorOriginRegionSet gamma gamma' := by
      simpa [rlc_connectorOriginRegion] using htRegion
    have htAllowed := (Finset.mem_sdiff.mp htSet.1).1
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at htAllowed ⊢
    rw [mem_rect] at htAllowed ⊢
    have hn := hfaith.scale_pos
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at htAllowed ⊢
    omega
  rw [rlc_connectorEdges, Finset.mem_filter]
  exact ⟨by
    rw [mem_edgesWithinFinset]
    exact ⟨![-1, t], hleftBox, ![0, t], htBox, rfl⟩,
    ⟨![0, t], htRegion, Sym2.mem_mk_right _ _⟩⟩


theorem rlc_bookFaithful_axisIntervalVertical_mem_connectorEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (t : Int)
    (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
    (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
    s((![0, t] : Site 2), ![0, t + 1]) ∈
      rlc_connectorEdges gamma gamma' := by
  have hrightNeg := hfaith.right_axis_strict
  have hleftPos := hfaith.left_axis_strict
  have htBox : (![0, t] : Site 2) ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hrightBox := gamma.1.1.2.1
    have hleftBox := gamma'.1.2.1.2.1
    rw [mem_rect] at hrightBox hleftBox
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have ht1Box : (![0, t + 1] : Site 2) ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hrightBox := gamma.1.1.2.1
    have hleftBox := gamma'.1.2.1.2.1
    rw [mem_rect] at hrightBox hleftBox
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hregion : (![0, t] : Site 2) ∈
        rlc_connectorOriginRegion gamma gamma' ∨
      (![0, t + 1] : Site 2) ∈
        rlc_connectorOriginRegion gamma gamma' := by
    by_cases ht : (gamma.1.1 : Site 2) 1 < t
    · exact Or.inl (hfaith.axisGap_mem_connectorOriginRegion
        t ht (by omega))
    · right
      apply hfaith.axisGap_mem_connectorOriginRegion (t + 1)
      · omega
      · omega
  rw [rlc_connectorEdges, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [mem_edgesWithinFinset]
    exact ⟨![0, t], htBox, ![0, t + 1], ht1Box, rfl⟩
  · rcases hregion with htRegion | ht1Region
    · exact ⟨![0, t], htRegion, Sym2.mem_mk_left _ _⟩
    · exact ⟨![0, t + 1], ht1Region, Sym2.mem_mk_right _ _⟩


theorem rlc_bookFaithful_axisInterval_cutCrossing
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A : Set (Site 2))
    (hAright : ∀ z ∈ rlc_pathVertices gamma.1, z ∈ A)
    (hAleft : ∀ z ∈ rlc_pathVertices gamma'.1, z ∉ A) :
    ∃ t : Int,
      (gamma.1.1 : Site 2) 1 ≤ t ∧
      t + 1 ≤ (gamma'.1.2.1 : Site 2) 1 ∧
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
        s((![0, t] : Site 2), ![0, t + 1]) ∧
      s((![0, t] : Site 2), ![0, t + 1]) ∈
        rlc_connectorEdges gamma gamma' ∧
      (t = (gamma.1.1 : Site 2) 1 ∨
        rlc_pimsEdgeEquiv s((![0, t] : Site 2), ![0, t + 1]) ∈
          rlc_connectorEdges gamma gamma') := by
  let x : Site 2 := gamma.1.1
  let y : Site 2 := gamma'.1.2.1
  have hx0 : x 0 = 0 := gamma.1.1.2.2
  have hy0 : y 0 = 0 := gamma'.1.2.1.2.2
  have hxy : x 1 ≤ y 1 := le_of_lt hfaith.axis_contacts_strict
  have hxx : x = ![0, x 1] := by
    ext i
    fin_cases i <;> simp [hx0]
  have hyy : y = ![0, y 1] := by
    ext i
    fin_cases i <;> simp [hy0]
  let w : (hypercubicLattice 2).Walk x y :=
    (sw_vertSeg 0 (x 1) (y 1)).copy hxx.symm hyy.symm
  have hxA : x ∈ A := hAright x (rlc_path_start_mem_vertices gamma.1)
  have hyA : y ∉ A := hAleft y
    (rlc_connector_path_end_mem_vertices gamma'.1)
  obtain ⟨u, v, huvEdge, huA, hvA⟩ :=
    rlc_walk_pred_first_exit w (fun z => z ∈ A) hxA hyA
  have huvAdj : (hypercubicLattice 2).Adj u v :=
    w.adj_of_mem_edges huvEdge
  have huSupp := w.fst_mem_support_of_mem_edges huvEdge
  have hvSupp := w.snd_mem_support_of_mem_edges huvEdge
  have support_data (z : Site 2) (hz : z ∈ w.support) :
      z 0 = 0 ∧ x 1 ≤ z 1 ∧ z 1 ≤ y 1 := by
    have hz' : z ∈ (sw_vertSeg 0 (x 1) (y 1)).support := by
      simpa [w, SimpleGraph.Walk.support_copy] using hz
    rw [sw_vertSeg_mem_support] at hz'
    obtain ⟨k, hk, hzk⟩ := hz'
    rw [Set.uIcc_of_le hxy] at hk
    have hz0 : z 0 = 0 := by rw [hzk]; simp
    have hz1 : z 1 = k := by rw [hzk]; simp
    exact ⟨hz0, hz1.symm ▸ hk.1, hz1.symm ▸ hk.2⟩
  obtain ⟨hu0, hxu, huy⟩ := support_data u huSupp
  obtain ⟨hv0, hxv, hvy⟩ := support_data v hvSupp
  dsimp only [x, y] at hxu huy hxv hvy
  have huEq : u = (![0, u 1] : Site 2) := by
    ext i
    fin_cases i <;> simp [hu0]
  have hvEq : v = (![0, v 1] : Site 2) := by
    ext i
    fin_cases i <;> simp [hv0]
  rcases adj_cases huvAdj with hvertical | hhorizontal
  · rcases hvertical.2 with huvHeight | hvuHeight
    · let t := v 1
      have hedge : s(u, v) =
          s((![0, t] : Site 2), ![0, t + 1]) := by
        dsimp only [t]
        rw [huEq, hvEq]
        simp only [Matrix.cons_val_one]
        rw [huvHeight]
        exact Sym2.eq_swap
      have hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut A s(u, v) :=
        ⟨u, v, rfl, Or.inl ⟨huA, hvA⟩⟩
      rw [hedge] at hcross
      have htarget := rlc_bookFaithful_axisIntervalVertical_mem_connectorEdges
        hfaith t (by dsimp only [t]; omega) (by dsimp only [t]; omega)
      refine ⟨t, by dsimp only [t]; omega, by dsimp only [t]; omega,
        hcross, htarget, ?_⟩
      by_cases ht : t = (gamma.1.1 : Site 2) 1
      · exact Or.inl ht
      · exact Or.inr
          (rlc_bookFaithful_axisGapVertical_preimage_mem_connectorEdges
            hfaith t (by dsimp only [t] at ht ⊢; omega)
              (by dsimp only [t]; omega))
    · let t := u 1
      have hedge : s(u, v) =
          s((![0, t] : Site 2), ![0, t + 1]) := by
        dsimp only [t]
        rw [huEq, hvEq]
        simp only [Matrix.cons_val_one]
        rw [hvuHeight]
        simp only [Matrix.cons_val_zero]
      have hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut A s(u, v) :=
        ⟨u, v, rfl, Or.inl ⟨huA, hvA⟩⟩
      rw [hedge] at hcross
      have htarget := rlc_bookFaithful_axisIntervalVertical_mem_connectorEdges
        hfaith t (by dsimp only [t]; omega) (by dsimp only [t]; omega)
      refine ⟨t, by dsimp only [t]; omega, by dsimp only [t]; omega,
        hcross, htarget, ?_⟩
      by_cases ht : t = (gamma.1.1 : Site 2) 1
      · exact Or.inl ht
      · exact Or.inr
          (rlc_bookFaithful_axisGapVertical_preimage_mem_connectorEdges
            hfaith t (by dsimp only [t] at ht ⊢; omega)
              (by dsimp only [t]; omega))
  · rcases hhorizontal with ⟨huvHeight, huv0 | hvu0⟩
    · omega
    · omega


theorem rlc_bookFaithful_lowerAxis_preimage_mem_reflectedRightPathEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    rlc_pimsEdgeEquiv
        s((![0, (gamma.1.1 : Site 2) 1] : Site 2),
          ![0, (gamma.1.1 : Site 2) 1 + 1]) ∈
      rlc_reflectedPathEdges gamma.1 := by
  let q := gamma.1.2.2.1
  have hne : (⟨gamma.1.1, leftSide_subset gamma.1.1.2⟩ :
      rect 0 (2 * n) (-n) n) ≠
      ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ := by
    intro h
    have h0 := congrArg
      (fun z : rect 0 (2 * n) (-n) n => (z : Site 2) 0) h
    have hx := gamma.1.1.2.2
    have hy := gamma.1.2.1.2.2
    have hn := hfaith.scale_pos
    norm_num at h0 hx hy
    omega
  obtain ⟨z, hz, tail, hq⟩ := q.exists_eq_cons_of_ne hne
  have hedge : s((gamma.1.1 : Site 2), (z : Site 2)) ∈
      rlc_pathEdges gamma.1 := by
    rw [rlc_pathEdges, Finset.mem_image]
    refine ⟨s(⟨gamma.1.1, leftSide_subset gamma.1.1.2⟩, z), ?_, rfl⟩
    change s(⟨gamma.1.1, leftSide_subset gamma.1.1.2⟩, z) ∈
      q.edges.toFinset
    rw [hq]
    apply List.mem_toFinset.mpr
    simp
  have hzPath : (z : Site 2) ∈ rlc_pathVertices gamma.1 :=
    (rlc_pathEdge_endpoints_mem_vertices gamma.1 hedge).2
  have hzNe : (z : Site 2) ≠ (gamma.1.1 : Site 2) := by
    intro h
    have hadj : (hypercubicLattice 2).Adj
        (gamma.1.1 : Site 2) (z : Site 2) := hz
    exact hadj.ne h.symm
  have hzPositive : 0 < (z : Site 2) 0 :=
    hfaith.right_vertex_strict hzPath hzNe
  have hstart0 : (gamma.1.1 : Site 2) 0 = 0 := gamma.1.1.2.2
  have hzEq : (z : Site 2) =
      (![1, (gamma.1.1 : Site 2) 1] : Site 2) := by
    have hadj : (hypercubicLattice 2).Adj
        (gamma.1.1 : Site 2) (z : Site 2) := hz
    rcases adj_cases hadj with hvertical | hhorizontal
    · omega
    · rcases hhorizontal with ⟨hheight, hleft | hright⟩
      · ext i
        fin_cases i <;> simp <;> omega
      · ext i
        fin_cases i <;> simp <;> omega
  rw [show rlc_pimsEdgeEquiv
      s((![0, (gamma.1.1 : Site 2) 1] : Site 2),
        ![0, (gamma.1.1 : Site 2) 1 + 1]) =
      s((![-1, (gamma.1.1 : Site 2) 1] : Site 2),
        ![0, (gamma.1.1 : Site 2) 1]) by
    simpa using rlc_pimsEdgeEquiv_vertical
      0 ((gamma.1.1 : Site 2) 1)]
  rw [rlc_reflectedPathEdges, Finset.mem_image]
  refine ⟨s((gamma.1.1 : Site 2), (z : Site 2)), hedge, ?_⟩
  rw [hzEq]
  have hstart : (gamma.1.1 : Site 2) =
      (![0, (gamma.1.1 : Site 2) 1] : Site 2) := by
    ext i
    fin_cases i <;> simp [hstart0]
  rw [hstart]
  simp [Sym2.map_mk, rlc_flipX, rlc_flipXFun, Sym2.eq_swap]


theorem rlc_bookFaithful_upperAxis_horizontal_mem_reflectedLeftPathEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    s((![0, (gamma'.1.2.1 : Site 2) 1] : Site 2),
      ![1, (gamma'.1.2.1 : Site 2) 1]) ∈
      rlc_reflectedPathEdges gamma'.1 := by
  let q := gamma'.1.2.2.1.reverse
  have hne :
      (⟨gamma'.1.2.1, rightSide_subset gamma'.1.2.1.2⟩ :
          rect (-2 * n) 0 (-n) n) ≠
        ⟨gamma'.1.1, leftSide_subset gamma'.1.1.2⟩ := by
    intro h
    have h0 := congrArg
      (fun z : rect (-2 * n) 0 (-n) n => (z : Site 2) 0) h
    have hx := gamma'.1.2.1.2.2
    have hy := gamma'.1.1.2.2
    have hn := hfaith.scale_pos
    norm_num at h0 hx hy
    omega
  obtain ⟨z, hz, tail, hq⟩ := q.exists_eq_cons_of_ne hne
  have hedge : s((z : Site 2), (gamma'.1.2.1 : Site 2)) ∈
      rlc_pathEdges gamma'.1 := by
    rw [rlc_pathEdges, Finset.mem_image]
    refine ⟨s(z,
      ⟨gamma'.1.2.1, rightSide_subset gamma'.1.2.1.2⟩), ?_, ?_⟩
    · change s(z,
        ⟨gamma'.1.2.1, rightSide_subset gamma'.1.2.1.2⟩) ∈
          gamma'.1.2.2.1.edges.toFinset
      apply List.mem_toFinset.mpr
      have hrev : s(⟨gamma'.1.2.1,
          rightSide_subset gamma'.1.2.1.2⟩, z) ∈ q.edges := by
        rw [hq]
        simp
      simpa [q, SimpleGraph.Walk.edges_reverse, Sym2.eq_swap] using hrev
    · simp [Sym2.map_mk]
  have hzPath : (z : Site 2) ∈ rlc_pathVertices gamma'.1 :=
    (rlc_pathEdge_endpoints_mem_vertices gamma'.1 hedge).1
  have hzNe : (z : Site 2) ≠ (gamma'.1.2.1 : Site 2) := by
    intro h
    have hadj : (hypercubicLattice 2).Adj
        (gamma'.1.2.1 : Site 2) (z : Site 2) := hz
    exact hadj.ne h.symm
  have hzNegative : (z : Site 2) 0 < 0 :=
    hfaith.left_vertex_strict hzPath hzNe
  have hend0 : (gamma'.1.2.1 : Site 2) 0 = 0 :=
    gamma'.1.2.1.2.2
  have hzEq : (z : Site 2) =
      (![-1, (gamma'.1.2.1 : Site 2) 1] : Site 2) := by
    have hadj : (hypercubicLattice 2).Adj
        (gamma'.1.2.1 : Site 2) (z : Site 2) := hz
    rcases adj_cases hadj with hvertical | hhorizontal
    · omega
    · rcases hhorizontal with ⟨hheight, hleft | hright⟩
      · ext i
        fin_cases i <;> simp <;> omega
      · ext i
        fin_cases i <;> simp <;> omega
  rw [rlc_reflectedPathEdges, Finset.mem_image]
  refine ⟨s((z : Site 2), (gamma'.1.2.1 : Site 2)), hedge, ?_⟩
  rw [hzEq]
  have hend : (gamma'.1.2.1 : Site 2) =
      (![0, (gamma'.1.2.1 : Site 2) 1] : Site 2) := by
    ext i
    fin_cases i <;> simp [hend0]
  rw [hend]
  simp [Sym2.map_mk, rlc_flipX, rlc_flipXFun, Sym2.eq_swap]


theorem rlc_bookFaithful_upperAxis_horizontal_mem_originalLeftPathEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    s((![-1, (gamma'.1.2.1 : Site 2) 1] : Site 2),
      ![0, (gamma'.1.2.1 : Site 2) 1]) ∈ rlc_pathEdges gamma'.1 := by
  have href :=
    rlc_bookFaithful_upperAxis_horizontal_mem_reflectedLeftPathEdges hfaith
  rw [rlc_reflectedPathEdges, Finset.mem_image] at href
  obtain ⟨e, he, hmap⟩ := href
  have hcanonical : Sym2.map rlc_flipX
      s((![-1, (gamma'.1.2.1 : Site 2) 1] : Site 2),
        ![0, (gamma'.1.2.1 : Site 2) 1]) =
      s((![0, (gamma'.1.2.1 : Site 2) 1] : Site 2),
        ![1, (gamma'.1.2.1 : Site 2) 1]) := by
    simp [Sym2.map_mk, rlc_flipX, rlc_flipXFun, Sym2.eq_swap]
  have heq : e =
      s((![-1, (gamma'.1.2.1 : Site 2) 1] : Site 2),
        ![0, (gamma'.1.2.1 : Site 2) 1]) := by
    apply Sym2.map.injective rlc_flipX.injective
    exact hmap.trans hcanonical.symm
  simpa [heq] using he


theorem rlc_bookFaithful_upperAxis_horizontal_twoChannelWitness
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      target.1.map Subtype.val =
        s((![0, (gamma'.1.2.1 : Site 2) 1] : Site 2),
          ![1, (gamma'.1.2.1 : Site 2) 1]) := by
  let U := (gamma'.1.2.1 : Site 2) 1
  have hzeroBox : (![0, U] : Site 2) ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hbox := gamma'.1.2.1.2.1
    rw [mem_rect] at hbox
    have hn := hfaith.scale_pos
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have honeBox : (![1, U] : Site 2) ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hbox := gamma'.1.2.1.2.1
    rw [mem_rect] at hbox
    have hn := hfaith.scale_pos
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  let x : RlcConnectorVertex n := ⟨![0, U], by
    simpa [rlc_connectorBox] using hzeroBox⟩
  let y : RlcConnectorVertex n := ⟨![1, U], by
    simpa [rlc_connectorBox] using honeBox⟩
  have hlat : (hypercubicLattice 2).Adj (![0, U] : Site 2) ![1, U] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hreflected : s((![0, U] : Site 2), ![1, U]) ∈
      rlc_reflectedPathEdges gamma'.1 := by
    simpa [U] using
      rlc_bookFaithful_upperAxis_horizontal_mem_reflectedLeftPathEdges hfaith
  have hnotOriginal : ¬(rlc_connectorTraceWiring gamma gamma').Adj x y := by
    rintro ⟨_hlat, htrace⟩
    rw [Finset.mem_union] at htrace
    rcases htrace with hright | hleft
    · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
      have haxis := hfaith.right_axis_unique hends.1 (by simp [x])
      have hheight := congrArg (fun z : Site 2 => z 1) haxis
      have hstrict := hfaith.axis_contacts_strict
      change U = (gamma.1.1 : Site 2) 1 at hheight
      dsimp only [U] at hheight
      omega
    · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
      have hbox := rlc_pathVertex_mem_rect gamma'.1 hends.2
      rw [mem_rect] at hbox
      simp only [y, Matrix.cons_val_zero] at hbox
      omega
  have htwo : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y := by
    refine ⟨Or.inr ⟨by simpa [x, y] using hlat, ?_⟩, hnotOriginal⟩
    rw [rlc_connectorReflectedTraceEdges, Finset.mem_union]
    exact Or.inr (by simpa [x, y] using hreflected)
  let target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
    ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
  exact ⟨target, by simp [target, x, y, U, Sym2.map_mk]⟩


theorem rlc_bookFaithful_upperAxis_columnSource_twoChannel_or_original
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    (∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      source.1.map Subtype.val =
        s((![-1, (gamma'.1.2.1 : Site 2) 1 - 1] : Site 2),
          ![-1, (gamma'.1.2.1 : Site 2) 1])) ∨
      s((![-1, (gamma'.1.2.1 : Site 2) 1 - 1] : Site 2),
        ![-1, (gamma'.1.2.1 : Site 2) 1]) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  let U := (gamma'.1.2.1 : Site 2) 1
  have hlowerBox : (![-1, U - 1] : Site 2) ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hbox := gamma'.1.2.1.2.1
    rw [mem_rect] at hbox
    have hn := hfaith.scale_pos
    have hUpos := hfaith.left_axis_strict
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hupperBox : (![-1, U] : Site 2) ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hbox := gamma'.1.2.1.2.1
    rw [mem_rect] at hbox
    have hn := hfaith.scale_pos
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hlat : (hypercubicLattice 2).Adj
      (![-1, U - 1] : Site 2) ![-1, U] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hplanar : s((![-1, U - 1] : Site 2), ![-1, U]) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma' := by
    apply rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
      gamma gamma' hlat hlowerBox hupperBox
    · exact rlc_axisGapFace_mem_connectorCentralFaceRegion
        gamma gamma' hfaith (t := U - 1) (by
          have hstrict := hfaith.axis_contacts_strict
          dsimp only [U]
          omega) (by dsimp only [U]; omega)
    · simp [flankFaces]
  let x : RlcConnectorVertex n := ⟨![-1, U - 1], by
    simpa [rlc_connectorBox] using hlowerBox⟩
  let y : RlcConnectorVertex n := ⟨![-1, U], by
    simpa [rlc_connectorBox] using hupperBox⟩
  have hclosure : (rlc_connectorCentralFaceClosureGraph gamma gamma').Adj
      x y := ⟨by simpa [x, y] using hlat, by simpa [x, y] using hplanar⟩
  rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
    at hclosure
  rcases hclosure with htwo | htrace
  · left
    let source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
      ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
    exact ⟨source, by simp [source, x, y, U, Sym2.map_mk]⟩
  · right
    simpa [x, y, U] using htrace.2


theorem rlc_bookFaithful_upperAxis_fullPhysical_or_original
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    (∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      target.1.1.map Subtype.val =
          s((![0, (gamma'.1.2.1 : Site 2) 1] : Site 2),
            ![1, (gamma'.1.2.1 : Site 2) 1]) ∧
        (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val =
          s((![-1, (gamma'.1.2.1 : Site 2) 1 - 1] : Site 2),
            ![-1, (gamma'.1.2.1 : Site 2) 1])) ∨
      s((![-1, (gamma'.1.2.1 : Site 2) 1 - 1] : Site 2),
        ![-1, (gamma'.1.2.1 : Site 2) 1]) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  obtain ⟨target, htarget⟩ :=
    rlc_bookFaithful_upperAxis_horizontal_twoChannelWitness hfaith
  rcases rlc_bookFaithful_upperAxis_columnSource_twoChannel_or_original
      hfaith with ⟨source, hsource⟩ | htrace
  · left
    let physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' :=
      ⟨target, ⟨⟨source, by
        rw [htarget]
        simpa using hsource.trans
          (rlc_pimsEdgeEquiv_horizontal 0
            ((gamma'.1.2.1 : Site 2) 1)).symm⟩⟩⟩
    refine ⟨physical, htarget, ?_⟩
    exact rlc_twoChannelFullPhysicalSourceEdge_map physical |>.trans (by
      rw [htarget]
      simpa using rlc_pimsEdgeEquiv_horizontal 0
        ((gamma'.1.2.1 : Site 2) 1))
  · exact Or.inr htrace


theorem RlcBookFaithfulTracePair.axisFaceBand_mem_centralFaceRegion
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (k : Int)
    (hbelow : (gamma.1.1 : Site 2) 1 ≤ k)
    (habove : k < (gamma'.1.2.1 : Site 2) 1) :
    (![0, k] : Site 2) ∈
      rlc_connectorCentralFaceRegion gamma gamma' := by
  let z : Site 2 := ![0, k]
  let w : (hypercubicLattice 2).Walk rlc_connectorCentralFace z :=
    (sw_vertSeg 0 0 k).copy rfl rfl
  have hrightNeg := hfaith.right_axis_strict
  have hleftPos := hfaith.left_axis_strict
  have hsupp (f : Site 2) (hf : f ∈ w.support) :
      f 0 = 0 ∧
      (gamma.1.1 : Site 2) 1 ≤ f 1 ∧
      f 1 < (gamma'.1.2.1 : Site 2) 1 ∧
      f ∈ rlc_connectorFaceBox n := by
    have hf' : f ∈ (sw_vertSeg 0 0 k).support := by
      simpa [w, SimpleGraph.Walk.support_copy] using hf
    rw [sw_vertSeg_mem_support] at hf'
    obtain ⟨t, ht, hft⟩ := hf'
    have hf0 : f 0 = 0 := by rw [hft]; simp
    have hf1 : f 1 = t := by rw [hft]; simp
    have htBand : (gamma.1.1 : Site 2) 1 ≤ t ∧
        t < (gamma'.1.2.1 : Site 2) 1 := by
      rw [Set.mem_uIcc] at ht
      rcases ht with ht | ht <;> omega
    refine ⟨hf0, by omega, by omega, ?_⟩
    simp only [rlc_connectorFaceBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hrightBox := gamma.1.1.2.1
    have hleftBox := gamma'.1.2.1.2.1
    rw [mem_rect] at hrightBox hleftBox
    omega
  have hedge : ∀ e ∈ w.edges,
      e ∈ (rlc_connectorFourTraceFaceCutGraph gamma gamma').edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ f g =>
      have hfg := w.adj_of_mem_edges he
      have hf := hsupp f (w.fst_mem_support_of_mem_edges he)
      have hg := hsupp g (w.snd_mem_support_of_mem_edges he)
      rw [SimpleGraph.mem_edgeSet,
        rlc_connectorFourTraceFaceCutGraph_adj]
      refine ⟨hfg, ?_⟩
      intro htrace
      have hfEq : f = (![0, f 1] : Site 2) := by
        ext i
        fin_cases i <;> simp [hf.1]
      have hgEq : g = (![0, g 1] : Site 2) := by
        ext i
        fin_cases i <;> simp [hg.1]
      rcases adj_cases hfg with hvertical | hhorizontal
      · rcases hvertical.2 with hfgHeight | hgfHeight
        · have hshared : sharedPrimalEdge f g =
              s((![0, f 1] : Site 2), ![1, f 1]) := by
            rw [hfEq, hgEq,
              show g 1 = f 1 - 1 by omega,
              sharedPrimalEdge_bottom]
            simp [faceCorner00, faceCorner10]
          have haxisBarrier : (![0, f 1] : Site 2) ∈
              rlc_connectorBarrier gamma gamma' :=
            rlc_mem_connectorBarrier_of_mem_fourTraceEdge
              gamma gamma' htrace (by
                rw [hshared]
                exact Sym2.mem_mk_left _ _)
          rw [rlc_axis_mem_connectorBarrier_iff
            gamma gamma' (f 1)] at haxisBarrier
          rcases haxisBarrier with hright | hleft
          · have heq := hfaith.right_axis_unique hright (by simp)
            have hheight : f 1 = (gamma.1.1 : Site 2) 1 := by
              simpa using congrArg (fun u : Site 2 => u 1) heq
            omega
          · have heq := hfaith.left_axis_unique hleft (by simp)
            have hheight : f 1 = (gamma'.1.2.1 : Site 2) 1 := by
              simpa using congrArg (fun u : Site 2 => u 1) heq
            omega
        · have hshared : sharedPrimalEdge f g =
              s((![0, g 1] : Site 2), ![1, g 1]) := by
            rw [sharedPrimalEdge_comm_of_adj hfg, hfEq, hgEq,
              show f 1 = g 1 - 1 by omega,
              sharedPrimalEdge_bottom]
            simp [faceCorner00, faceCorner10]
          have haxisBarrier : (![0, g 1] : Site 2) ∈
              rlc_connectorBarrier gamma gamma' :=
            rlc_mem_connectorBarrier_of_mem_fourTraceEdge
              gamma gamma' htrace (by
                rw [hshared]
                exact Sym2.mem_mk_left _ _)
          rw [rlc_axis_mem_connectorBarrier_iff
            gamma gamma' (g 1)] at haxisBarrier
          rcases haxisBarrier with hright | hleft
          · have heq := hfaith.right_axis_unique hright (by simp)
            have hheight : g 1 = (gamma.1.1 : Site 2) 1 := by
              simpa using congrArg (fun u : Site 2 => u 1) heq
            omega
          · have heq := hfaith.left_axis_unique hleft (by simp)
            have hheight : g 1 = (gamma'.1.2.1 : Site 2) 1 := by
              simpa using congrArg (fun u : Site 2 => u 1) heq
            omega
      · rcases hhorizontal with ⟨hfgHeight, hfg0 | hgf0⟩
        · omega
        · omega
  let q : (rlc_connectorFourTraceFaceCutGraph gamma gamma').Walk
      rlc_connectorCentralFace z :=
    w.transfer (rlc_connectorFourTraceFaceCutGraph gamma gamma')
      (by
        intro e he
        exact hedge e he)
  have hqBox : ∀ f ∈ q.support, f ∈ rlc_connectorFaceBox n := by
    intro f hf
    have hfw : f ∈ w.support := by
      simpa [q, SimpleGraph.Walk.support_transfer] using hf
    exact (hsupp f hfw).2.2.2
  let qFinite := q.induce
    (rlc_connectorFaceBox n : Set (Site 2)) hqBox
  have hzBox : z ∈ rlc_connectorFaceBox n :=
    hqBox z q.end_mem_support
  have hcBox : rlc_connectorCentralFace ∈ rlc_connectorFaceBox n :=
    hqBox rlc_connectorCentralFace q.start_mem_support
  have hset : z ∈ rlc_connectorCentralFaceRegionSet gamma gamma' :=
    ⟨hzBox, hcBox, by
      change (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
        ⟨rlc_connectorCentralFace, hcBox⟩ ⟨z, hzBox⟩
      exact qFinite.reachable⟩
  simpa [rlc_connectorCentralFaceRegion] using hset


theorem rlc_bookFaithful_axisIntervalVertical_not_mem_originalTraceEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (t : Int)
    (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
    (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
    s((![0, t] : Site 2), ![0, t + 1]) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  intro htrace
  rw [Finset.mem_union] at htrace
  rcases htrace with hright | hleft
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
    have hfirst := hfaith.right_axis_unique hends.1 (by simp)
    have hsecond := hfaith.right_axis_unique hends.2 (by simp)
    have hfirstHeight := congrArg (fun z : Site 2 => z 1) hfirst
    have hsecondHeight := congrArg (fun z : Site 2 => z 1) hsecond
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      at hfirstHeight hsecondHeight
    omega
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
    have hfirst := hfaith.left_axis_unique hends.1 (by simp)
    have hsecond := hfaith.left_axis_unique hends.2 (by simp)
    have hfirstHeight := congrArg (fun z : Site 2 => z 1) hfirst
    have hsecondHeight := congrArg (fun z : Site 2 => z 1) hsecond
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      at hfirstHeight hsecondHeight
    omega


theorem rlc_bookFaithful_axisIntervalPreimage_not_mem_originalTraceEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (t : Int)
    (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
    (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
    s((![-1, t] : Site 2), ![0, t]) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  intro htrace
  rw [Finset.mem_union] at htrace
  rcases htrace with hright | hleft
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
    have hbox := rlc_pathVertex_mem_rect gamma.1 hends.1
    rw [mem_rect] at hbox
    simp only [Matrix.cons_val_zero] at hbox
    omega
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
    have haxis := hfaith.left_axis_unique hends.2 (by simp)
    have hheight := congrArg (fun z : Site 2 => z 1) haxis
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hheight
    omega


theorem rlc_bookFaithful_axisIntervalVertical_twoChannelWitness
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (t : Int)
    (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
    (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
    ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      target.1.map Subtype.val =
        s((![0, t] : Site 2), ![0, t + 1]) := by
  have hxBox : (![0, t] : Site 2) ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hrightBox := gamma.1.1.2.1
    have hleftBox := gamma'.1.2.1.2.1
    rw [mem_rect] at hrightBox hleftBox
    have hn := hfaith.scale_pos
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hyBox : (![0, t + 1] : Site 2) ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hrightBox := gamma.1.1.2.1
    have hleftBox := gamma'.1.2.1.2.1
    rw [mem_rect] at hrightBox hleftBox
    have hn := hfaith.scale_pos
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hlat : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hplanar : s((![0, t] : Site 2), ![0, t + 1]) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma' := by
    apply rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
      gamma gamma' hlat hxBox hyBox
      (hfaith.axisFaceBand_mem_centralFaceRegion t hbelow (by omega))
    simp [flankFaces]
  let x : RlcConnectorVertex n := ⟨![0, t], by
    simpa [rlc_connectorBox] using hxBox⟩
  let y : RlcConnectorVertex n := ⟨![0, t + 1], by
    simpa [rlc_connectorBox] using hyBox⟩
  have hclosure : (rlc_connectorCentralFaceClosureGraph gamma gamma').Adj
      x y := by
    exact ⟨by simpa [x, y] using hlat, by simpa [x, y] using hplanar⟩
  rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
    at hclosure
  rcases hclosure with htwo | htrace
  · let target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
      ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
    exact ⟨target, by simp [target, x, y, Sym2.map_mk]⟩
  · exfalso
    exact (rlc_bookFaithful_axisIntervalVertical_not_mem_originalTraceEdges
      hfaith t hbelow habove) (by simpa [x, y] using htrace.2)


theorem rlc_bookFaithful_axisIntervalPreimage_twoChannelWitness
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (t : Int)
    (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
    (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
    ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      source.1.map Subtype.val =
        s((![-1, t] : Site 2), ![0, t]) := by
  have hxBox : (![-1, t] : Site 2) ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hrightBox := gamma.1.1.2.1
    have hleftBox := gamma'.1.2.1.2.1
    rw [mem_rect] at hrightBox hleftBox
    have hn := hfaith.scale_pos
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hyBox : (![0, t] : Site 2) ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    have hrightBox := gamma.1.1.2.1
    have hleftBox := gamma'.1.2.1.2.1
    rw [mem_rect] at hrightBox hleftBox
    have hn := hfaith.scale_pos
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hlat : (hypercubicLattice 2).Adj
      (![-1, t] : Site 2) ![0, t] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  let x : RlcConnectorVertex n := ⟨![-1, t], by
    simpa [rlc_connectorBox] using hxBox⟩
  let y : RlcConnectorVertex n := ⟨![0, t], by
    simpa [rlc_connectorBox] using hyBox⟩
  have hnotOriginal : ¬(rlc_connectorTraceWiring gamma gamma').Adj x y := by
    rintro ⟨_hlat, htrace⟩
    exact (rlc_bookFaithful_axisIntervalPreimage_not_mem_originalTraceEdges
      hfaith t hbelow habove) (by simpa [x, y] using htrace)
  have htwo : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y := by
    by_cases ht : t = (gamma.1.1 : Site 2) 1
    · have hreflected : s((![-1, t] : Site 2), ![0, t]) ∈
          rlc_reflectedPathEdges gamma.1 := by
        subst t
        simpa only [rlc_pimsEdgeEquiv_vertical] using
          rlc_bookFaithful_lowerAxis_preimage_mem_reflectedRightPathEdges
            hfaith
      refine ⟨Or.inr ⟨by simpa [x, y] using hlat, ?_⟩, hnotOriginal⟩
      rw [rlc_connectorReflectedTraceEdges, Finset.mem_union]
      exact Or.inl (by simpa [x, y] using hreflected)
    · have hplanar : s((![-1, t] : Site 2), ![0, t]) ∈
          rlc_connectorCentralFacePlanarEdges gamma gamma' :=
        rlc_axisGapHorizontal_mem_connectorCentralFacePlanarEdges
          gamma gamma' hfaith (by omega) (by omega)
      have hclosure :
          (rlc_connectorCentralFaceClosureGraph gamma gamma').Adj x y :=
        ⟨by simpa [x, y] using hlat, by simpa [x, y] using hplanar⟩
      rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
        at hclosure
      exact hclosure.elim id (fun htrace => False.elim
        (hnotOriginal htrace))
  let source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
    ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
  exact ⟨source, by simp [source, x, y, Sym2.map_mk]⟩


theorem rlc_bookFaithful_axisInterval_fullPhysicalTarget
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (t : Int)
    (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
    (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
    ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      target.1.1.map Subtype.val =
        s((![0, t] : Site 2), ![0, t + 1]) := by
  obtain ⟨target, htarget⟩ :=
    rlc_bookFaithful_axisIntervalVertical_twoChannelWitness
      hfaith t hbelow habove
  obtain ⟨source, hsource⟩ :=
    rlc_bookFaithful_axisIntervalPreimage_twoChannelWitness
      hfaith t hbelow habove
  refine ⟨⟨target, ⟨⟨source, ?_⟩⟩⟩, htarget⟩
  rw [htarget]
  exact hsource.trans (rlc_pimsEdgeEquiv_vertical 0 t).symm


theorem rlc_twoChannelFullPhysical_goodBoundary_of_source_bdEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    {p q : Site 2}
    (hpq : (hypercubicLattice 2).Adj p q)
    (hsource : (rlc_twoChannelFullPhysicalSourceEdge target).1.map
      Subtype.val = s(p, q))
    (hbd : bdEdge
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega) s(p, q)) :
    ∃ f g : Site 2,
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Adj f g ∧
      sharedPrimalEdge f g = s(p, q) := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  have hflank : flankFaces p q ∈ (faceBoundaryGraph H).edgeSet :=
    (phb_flankFaces_mem_faceBoundaryGraph_iff hpq).2 hbd
  induction hedge : flankFaces p q using Sym2.inductionOn with
  | _ f g =>
      have hfg : (faceBoundaryGraph H).Adj f g := by
        rw [hedge] at hflank
        exact hflank
      have hshared : sharedPrimalEdge f g = s(p, q) := by
        have hsps := symPrimalSym_flankFaces hpq
        rw [hedge, symPrimalSym_mk,
          symPrimal_eq_shared hfg.1] at hsps
        exact hsps
      have htarget : target.1.1.map Subtype.val =
          s(rlc_dualReflect f, rlc_dualReflect g) := by
        apply rlc_pimsEdgeEquiv.injective
        calc
          rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) =
              (rlc_twoChannelFullPhysicalSourceEdge target).1.map
                Subtype.val :=
            (rlc_twoChannelFullPhysicalSourceEdge_map target).symm
          _ = s(p, q) := hsource
          _ = sharedPrimalEdge f g := hshared.symm
          _ = rlc_pimsEdgeEquiv
              s(rlc_dualReflect f, rlc_dualReflect g) :=
            (rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg.1).symm
      have hcarrier : RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' f g :=
        ⟨target.1, rlc_twoChannelFullPhysicalSourceEdge target,
          htarget, hsource.trans hshared.symm⟩
      exact ⟨f, g,
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).2 ⟨hfg, hcarrier⟩, hshared⟩


theorem rlc_bookFaithful_fullFilledAxisExit_carrier_or_top
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ (t : Int) (f g : Site 2),
      (gamma.1.1 : Site 2) 1 ≤ t ∧
        t + 1 ≤ (gamma'.1.2.1 : Site 2) 1 ∧
        (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g ∧
        sharedPrimalEdge f g =
          s((![0, t] : Site 2), ![0, t + 1]) ∧
        (RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' f g ∨
          t + 1 = (gamma'.1.2.1 : Site 2) 1) := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  have hright : ∀ z ∈ rlc_pathVertices gamma.1, z ∈ H := by
    intro z hz
    exact rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
      (rlc_rightPathVertex_mem_twoChannelFullReachSet
        gamma gamma' omega hz)
  have hleft : ∀ z ∈ rlc_pathVertices gamma'.1, z ∉ H := by
    intro z hz hzH
    have hzExt := rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hz
    exact hzH hzExt
  obtain ⟨t, hbelow, habove, hcross, _htarget, _hsource⟩ :=
    rlc_bookFaithful_axisInterval_cutCrossing hfaith H hright hleft
  let p : Site 2 := ![0, t]
  let q : Site 2 := ![0, t + 1]
  have hpq : (hypercubicLattice 2).Adj p q := by
    simp [p, q, hypercubicLattice_adj, Fin.sum_univ_two]
  have hbd : bdEdge H s(p, q) := by
    obtain ⟨u, v, huv, hsep⟩ := hcross
    change s(p, q) = s(u, v) at huv
    rw [Sym2.eq_iff] at huv
    rw [bdEdge_mk]
    rcases huv with ⟨hpu, hqv⟩ | ⟨hpv, hqu⟩
    · subst u
      subst v
      tauto
    · subst v
      subst u
      tauto
  have hflank : flankFaces p q ∈ (faceBoundaryGraph H).edgeSet :=
    (phb_flankFaces_mem_faceBoundaryGraph_iff hpq).2 hbd
  induction hedge : flankFaces p q using Sym2.inductionOn with
  | _ f g =>
      have hfg : (faceBoundaryGraph H).Adj f g := by
        rw [hedge] at hflank
        exact hflank
      have hshared : sharedPrimalEdge f g = s(p, q) := by
        have hsps := symPrimalSym_flankFaces hpq
        rw [hedge, symPrimalSym_mk,
          symPrimal_eq_shared hfg.1] at hsps
        exact hsps
      refine ⟨t, f, g, hbelow, habove, hfg, by simpa [p, q] using hshared,
        ?_⟩
      by_cases htop : t + 1 = (gamma'.1.2.1 : Site 2) 1
      · exact Or.inr htop
      · left
        obtain ⟨target, htarget⟩ :=
          rlc_bookFaithful_axisIntervalPreimage_twoChannelWitness
            hfaith (t + 1) (by omega) (by omega)
        obtain ⟨source, hsource⟩ :=
          rlc_bookFaithful_axisIntervalVertical_twoChannelWitness
            hfaith t hbelow habove
        refine ⟨target, source, ?_, ?_⟩
        · apply rlc_pimsEdgeEquiv.injective
          calc
            rlc_pimsEdgeEquiv (target.1.map Subtype.val) =
                s((![0, t] : Site 2), ![0, t + 1]) := by
              rw [htarget]
              simpa using rlc_pimsEdgeEquiv_horizontal (-1) (t + 1)
            _ = sharedPrimalEdge f g := by simpa [p, q] using hshared.symm
            _ = rlc_pimsEdgeEquiv
                s(rlc_dualReflect f, rlc_dualReflect g) :=
              (rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg.1).symm
        · exact hsource.trans (by simpa [p, q] using hshared.symm)


theorem rlc_bookFaithful_fullFilledBoundary_physicalAxisAnchor
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ f g : Site 2,
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Adj f g := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  obtain ⟨t, f, g, hbelow, habove, hfg, hshared,
      hcarrier | htop⟩ :=
    rlc_bookFaithful_fullFilledAxisExit_carrier_or_top
      hfaith omega hno
  · exact ⟨f, g,
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).2 ⟨hfg, hcarrier⟩⟩
  · let U := (gamma'.1.2.1 : Site 2) 1
    have ht : t = U - 1 := by dsimp only [U]; omega
    have hzeroTopPath : (![0, U] : Site 2) ∈
        rlc_pathVertices gamma'.1 := by
      have haxis : (![0, U] : Site 2) = gamma'.1.2.1 := by
        ext i
        fin_cases i <;> simp [U, gamma'.1.2.1.2.2]
      rw [haxis]
      exact rlc_connector_path_end_mem_vertices gamma'.1
    have hzeroTopOut : (![0, U] : Site 2) ∉ H := by
      have hext := rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
        gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno
          hzeroTopPath
      exact fun hmem => hmem hext
    have hzeroLowerIn : (![0, U - 1] : Site 2) ∈ H := by
      have hbd := hfg.2
      rw [hshared, bdEdge_mk] at hbd
      have : (![0, t] : Site 2) ∈ H := hbd.mpr (by
        simpa [U, htop] using hzeroTopOut)
      simpa [ht] using this
    have hminusTopPath : (![-1, U] : Site 2) ∈
        rlc_pathVertices gamma'.1 := by
      have hedge :=
        rlc_bookFaithful_upperAxis_horizontal_mem_originalLeftPathEdges
          hfaith
      have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hedge
      simpa [U] using hends.1
    have hminusTopOut : (![-1, U] : Site 2) ∉ H := by
      have hext := rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
        gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno
          hminusTopPath
      exact fun hmem => hmem hext
    have horizontalAnchor
        (hminusLowerOut : (![-1, U - 1] : Site 2) ∉ H) :
        ∃ a b : Site 2,
          (rlc_twoChannelFullPhysicalGoodBoundaryGraph
            gamma gamma' omega).Adj a b := by
      obtain ⟨target, htarget⟩ :=
        rlc_bookFaithful_axisInterval_fullPhysicalTarget
          hfaith (U - 1) (by dsimp only [U]; omega) (by omega)
      have htarget' := htarget
      rw [show U - 1 + 1 = U by omega] at htarget'
      have hsource : (rlc_twoChannelFullPhysicalSourceEdge target).1.map
          Subtype.val =
          s((![-1, U - 1] : Site 2), ![0, U - 1]) := by
        calc
          _ = rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) :=
            rlc_twoChannelFullPhysicalSourceEdge_map target
          _ = rlc_pimsEdgeEquiv
              s((![0, U - 1] : Site 2), ![0, U] ) := by rw [htarget']
          _ = _ := by simpa using rlc_pimsEdgeEquiv_vertical 0 (U - 1)
      have hadj : (hypercubicLattice 2).Adj
          (![-1, U - 1] : Site 2) ![0, U - 1] := by
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      have hbd : bdEdge H
          s((![-1, U - 1] : Site 2), ![0, U - 1]) := by
        rw [bdEdge_mk]
        simp [hminusLowerOut, hzeroLowerIn]
      obtain ⟨a, b, hab, _hshared⟩ :=
        rlc_twoChannelFullPhysical_goodBoundary_of_source_bdEdge
          omega target hadj hsource hbd
      exact ⟨a, b, hab⟩
    rcases
        rlc_bookFaithful_upperAxis_columnSource_twoChannel_or_original
          hfaith with ⟨source, hsource⟩ | htrace
    · by_cases hminusLowerIn : (![-1, U - 1] : Site 2) ∈ H
      · obtain ⟨target, htarget⟩ :=
          rlc_bookFaithful_upperAxis_horizontal_twoChannelWitness hfaith
        let physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' :=
          ⟨target, ⟨⟨source, by
            rw [htarget]
            simpa [U] using hsource.trans
              (rlc_pimsEdgeEquiv_horizontal 0 U).symm⟩⟩⟩
        have hadj : (hypercubicLattice 2).Adj
            (![-1, U - 1] : Site 2) ![-1, U] := by
          simp [hypercubicLattice_adj, Fin.sum_univ_two]
        have hsourcePhysical :
            (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
              Subtype.val =
              s((![-1, U - 1] : Site 2), ![-1, U]) := by
          exact rlc_twoChannelFullPhysicalSourceEdge_map physical |>.trans
            (by rw [htarget]; simpa [U] using
              rlc_pimsEdgeEquiv_horizontal 0 U)
        have hbd : bdEdge H
            s((![-1, U - 1] : Site 2), ![-1, U]) := by
          rw [bdEdge_mk]
          simp [hminusLowerIn, hminusTopOut]
        obtain ⟨a, b, hab, _hshared⟩ :=
          rlc_twoChannelFullPhysical_goodBoundary_of_source_bdEdge
            omega physical hadj hsourcePhysical hbd
        exact ⟨a, b, hab⟩
      · exact horizontalAnchor hminusLowerIn
    · apply horizontalAnchor
      rw [Finset.mem_union] at htrace
      rcases htrace with hright | hleft
      · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
        have hbox := rlc_pathVertex_mem_rect gamma.1 hends.1
        rw [mem_rect] at hbox
        simp only [Matrix.cons_val_zero] at hbox
        omega
      · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
        have hext :=
          rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
            gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno
              hends.1
        exact fun hmem => hmem hext


theorem rlc_bookFaithful_fullFilledBoundary_axisAnchorPaths
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ (f g x y : Site 2),
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Adj f g ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      Nonempty ((faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk f x) ∧
      Nonempty ((faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk f y) := by
  obtain ⟨f, g, hfg⟩ :=
    rlc_bookFaithful_fullFilledBoundary_physicalAxisAnchor
      hfaith omega hno
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith omega hno
  have hfSupport : f ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support :=
    hfg.1.mem_support_left
  have hfx := rlc_twoChannelFullFilledFaceBoundary_reachable
    gamma gamma' omega hfSupport hxSupport
  have hfy := rlc_twoChannelFullFilledFaceBoundary_reachable
    gamma gamma' omega hfSupport hySupport
  exact ⟨f, g, x, y, hfg, hxPath, hyPath, hfx, hfy⟩


theorem rlc_bookFaithful_goodComponent_or_axisAnchorFirstExit
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨
      ∃ (f g z u v : Site 2)
        (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Walk f u)
        (r : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v z),
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Adj f g ∧
        (rlc_dualReflect z ∈ rlc_pathVertices gamma.1 ∨
          rlc_dualReflect z ∈ rlc_pathVertices gamma'.1) ∧
        (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' u v := by
  obtain ⟨f, g, x, y, hanchor, hxPath, hyPath, ⟨wx⟩, ⟨wy⟩⟩ :=
    rlc_bookFaithful_fullFilledBoundary_axisAnchorPaths
      hfaith omega hno
  let G := rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega
  by_cases hfx : G.Reachable f x
  · by_cases hfy : G.Reachable f y
    · exact Or.inl ⟨x, y, hfx.symm.trans hfy, hxPath, hyPath⟩
    · right
      rcases rlc_walk_subgraph_lift_or_first_exit_decomp
          (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma' omega) wy with
        ⟨qy, hqy⟩ | ⟨u, v, q, r, huv, huvBad, _hdecomp⟩
      · exact False.elim (hfy qy.reachable)
      · refine ⟨f, g, y, u, v, q, r, hanchor, Or.inr hyPath, huv, ?_⟩
        intro hcarrier
        exact huvBad
          ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
            gamma gamma' omega).2 ⟨huv, hcarrier⟩)
  · right
    rcases rlc_walk_subgraph_lift_or_first_exit_decomp
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma' omega) wx with
      ⟨qx, hqx⟩ | ⟨u, v, q, r, huv, huvBad, _hdecomp⟩
    · exact False.elim (hfx qx.reachable)
    · refine ⟨f, g, x, u, v, q, r, hanchor, Or.inl hxPath, huv, ?_⟩
      intro hcarrier
      exact huvBad
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).2 ⟨huv, hcarrier⟩)


theorem rlc_bookFaithful_staticCut_goodBoundaryAxisEdge_or_top
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
    ∃ (t : Int) (f g : Site 2),
      (gamma.1.1 : Site 2) 1 ≤ t ∧
        t + 1 ≤ (gamma'.1.2.1 : Site 2) 1 ∧
        sharedPrimalEdge f g =
          s((![0, t] : Site 2), ![0, t + 1]) ∧
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig
            gamma gamma' A)).Adj f g ∨
          t + 1 = (gamma'.1.2.1 : Site 2) 1) := by
  let omega := rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
    rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
  obtain ⟨t, f, g, hbelow, habove, hfg, hshared, hcarrier | htop⟩ :=
    rlc_bookFaithful_fullFilledAxisExit_carrier_or_top
      hfaith omega hno
  · refine ⟨t, f, g, hbelow, habove, hshared, Or.inl ?_⟩
    exact
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).2 ⟨hfg, hcarrier⟩
  · exact ⟨t, f, g, hbelow, habove, hshared, Or.inr htop⟩


theorem rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff
    {n : Int} (A : Set (RlcConnectorVertex n))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_twoChannelFullPhysicalEdgeCrossesCut A e ↔
      rlc_twoChannelFullPhysicalEdgeCrossesCut
        (rlc_twoChannelFullPhysicalLiftVertexCut A)
        (e.map Subtype.val) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [rlc_twoChannelFullPhysicalEdgeCrossesCut, Sym2.map_mk,
        Sym2.eq_iff,
        rlc_twoChannelFullPhysicalLiftVertexCut_mem]
      constructor
      · rintro ⟨u, v, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hcross⟩
        · refine ⟨x.1, y.1, Or.inl ⟨rfl, rfl⟩, ?_⟩
          simpa only [rlc_twoChannelFullPhysicalLiftVertexCut_mem] using hcross
        · refine ⟨y.1, x.1, Or.inr ⟨rfl, rfl⟩, ?_⟩
          simpa only [rlc_twoChannelFullPhysicalLiftVertexCut_mem] using hcross
      · rintro ⟨u, v, (⟨hxu, hyv⟩ | ⟨hxv, hyu⟩), hcross⟩
        · subst u
          subst v
          refine ⟨x, y, Or.inl ⟨rfl, rfl⟩, ?_⟩
          simpa only [rlc_twoChannelFullPhysicalLiftVertexCut_mem] using hcross
        · subst v
          subst u
          refine ⟨y, x, Or.inr ⟨rfl, rfl⟩, ?_⟩
          simpa only [rlc_twoChannelFullPhysicalLiftVertexCut_mem] using hcross


theorem rlc_twoChannelFullPhysical_goodBoundary_B_monochromatic_of_noPair
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {f g : Site 2}
    (hfg : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Adj f g) :
    (rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔
      rlc_dualReflect g ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) := by
  have hcarrier : RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' f g :=
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).1
          hfg |>.2
  obtain ⟨target, htarget, hsourceCross⟩ :=
    rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut
      gamma gamma' A hAright hAleft hfg.1 hcarrier
  have hnotAmbient : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        s(rlc_dualReflect f, rlc_dualReflect g) := by
    intro hcross
    have htargetAmbient : rlc_twoChannelFullPhysicalEdgeCrossesCut
        (rlc_twoChannelFullPhysicalLiftVertexCut B)
          (target.1.1.map Subtype.val) := by
      rwa [htarget]
    have htargetCross : rlc_twoChannelFullPhysicalEdgeCrossesCut
        B target.1.1 :=
      (rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff
        B target.1.1).2 htargetAmbient
    exact hnoPair ⟨target, hsourceCross, htargetCross⟩
  have hmono :=
    (rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        s(rlc_dualReflect f, rlc_dualReflect g)).1 hnotAmbient
  exact hmono (rlc_dualReflect f) (rlc_dualReflect g) rfl


theorem rlc_twoChannelFullPhysical_goodWalk_B_monochromatic_of_noPair
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {f g : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk f g) :
    (rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔
      rlc_dualReflect g ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) := by
  induction q with
  | nil => rfl
  | @cons a b c hab q ih =>
      exact (rlc_twoChannelFullPhysical_goodBoundary_B_monochromatic_of_noPair
        gamma gamma' A B hAright hAleft hnoPair hab).trans ih


theorem rlc_twoChannelFullPhysical_noGoodComponent_of_noPair
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1) :
    ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
  rintro ⟨x, y, hxy, hxPath, hyPath⟩
  obtain ⟨q⟩ := hxy
  have hmono :=
    rlc_twoChannelFullPhysical_goodWalk_B_monochromatic_of_noPair
      gamma gamma' A B hAright hAleft hnoPair q
  have hxBox : rlc_dualReflect x ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_rightPathVertex_mem_connectorBox gamma hxPath
  have hxB : rlc_dualReflect x ∈
      rlc_twoChannelFullPhysicalLiftVertexCut B :=
    ⟨hxBox, hBright ⟨rlc_dualReflect x, hxBox⟩ hxPath⟩
  have hyB : rlc_dualReflect y ∉
      rlc_twoChannelFullPhysicalLiftVertexCut B := by
    rintro ⟨hyBox, hyB⟩
    exact hBleft ⟨rlc_dualReflect y, hyBox⟩ hyPath hyB
  exact hyB (hmono.mp hxB)


theorem rlc_twoChannelFullPhysical_goodPrefixEndpoints_B_separated_of_noPair
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {x y ur ul : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul) :
    rlc_dualReflect ur ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ∧
      rlc_dualReflect ul ∉ rlc_twoChannelFullPhysicalLiftVertexCut B := by
  have hxBox : rlc_dualReflect x ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_rightPathVertex_mem_connectorBox gamma hxPath
  have hxB : rlc_dualReflect x ∈
      rlc_twoChannelFullPhysicalLiftVertexCut B :=
    ⟨hxBox, hBright ⟨rlc_dualReflect x, hxBox⟩ hxPath⟩
  have hyB : rlc_dualReflect y ∉
      rlc_twoChannelFullPhysicalLiftVertexCut B := by
    rintro ⟨hyBox, hyB⟩
    exact hBleft ⟨rlc_dualReflect y, hyBox⟩ hyPath hyB
  have hmonoR :=
    rlc_twoChannelFullPhysical_goodWalk_B_monochromatic_of_noPair
      gamma gamma' A B hAright hAleft hnoPair qr
  have hmonoL :=
    rlc_twoChannelFullPhysical_goodWalk_B_monochromatic_of_noPair
      gamma gamma' A B hAright hAleft hnoPair ql
  exact ⟨hmonoR.mp hxB, fun hulB => hyB (hmonoL.mpr hulB)⟩


theorem rlc_twoChannelFullPhysical_contactCycle_BChanging_noncarrier_of_noPair
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ∃ f g : Site 2,
      s(f, g) ∈ c.edges ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' f g := by
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hxBox : rlc_dualReflect x ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_rightPathVertex_mem_connectorBox gamma hxPath
  have hxB : rlc_dualReflect x ∈
      rlc_twoChannelFullPhysicalLiftVertexCut B :=
    ⟨hxBox, hBright ⟨rlc_dualReflect x, hxBox⟩ hxPath⟩
  have hyB : rlc_dualReflect y ∉
      rlc_twoChannelFullPhysicalLiftVertexCut B := by
    rintro ⟨hyBox, hyB⟩
    exact hBleft ⟨rlc_dualReflect y, hyBox⟩ hyPath hyB
  let a := rlc_orderedContourArc c hx hy
  obtain ⟨f, g, hfg, hfB, hgB⟩ :=
    rlc_walk_pred_first_exit a
      (fun z => rlc_dualReflect z ∈
        rlc_twoChannelFullPhysicalLiftVertexCut B) hxB hyB
  have hfgCycle : s(f, g) ∈ c.edges :=
    rlc_orderedContourArc_edges_subset c hx hy hfg
  have hfgBoundary : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g :=
    a.adj_of_mem_edges hfg
  have hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' f g := by
    intro hcarrier
    have hgood : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Adj f g :=
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).2 ⟨hfgBoundary, hcarrier⟩
    have hmono :=
      rlc_twoChannelFullPhysical_goodBoundary_B_monochromatic_of_noPair
        gamma gamma' A B hAright hAleft hnoPair hgood
    exact hgB (hmono.mp hfB)
  exact ⟨f, g, hfgCycle,
    ⟨rlc_dualReflect f, rlc_dualReflect g, rfl,
      Or.inl ⟨hfB, hgB⟩⟩, hbad⟩


theorem
    rlc_twoChannelFullPhysical_BChanging_terminalClassification_of_noPair
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj f g)
    (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        s(rlc_dualReflect f, rlc_dualReflect g)) :
    ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g ∨
      ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
        target.1.map Subtype.val =
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
          rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
          ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
            gamma gamma' f g := by
  by_cases htarget : RlcTwoChannelFullPhysicalTargetCarrierGeometry
      gamma gamma' f g
  · right
    obtain ⟨target, htargetMap⟩ := htarget
    have htargetCrossAmbient : rlc_twoChannelFullPhysicalEdgeCrossesCut
        (rlc_twoChannelFullPhysicalLiftVertexCut B)
          (target.1.map Subtype.val) := by
      rw [htargetMap]
      exact hcrossB
    have htargetCross : rlc_twoChannelFullPhysicalEdgeCrossesCut
        B target.1 :=
      (rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff
        B target.1).2 htargetCrossAmbient
    refine ⟨target, htargetMap, htargetCross, ?_⟩
    intro hsource
    have hcarrier : RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
        gamma gamma' f g :=
      (rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
        gamma gamma' f g).2 ⟨⟨target, htargetMap⟩, hsource⟩
    obtain ⟨physical, hphysicalMap, hsourceCross⟩ :=
      rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut
        gamma gamma' A hAright hAleft hfg hcarrier
    have hphysicalCrossAmbient : rlc_twoChannelFullPhysicalEdgeCrossesCut
        (rlc_twoChannelFullPhysicalLiftVertexCut B)
          (physical.1.1.map Subtype.val) := by
      rw [hphysicalMap]
      exact hcrossB
    have hphysicalCross : rlc_twoChannelFullPhysicalEdgeCrossesCut
        B physical.1.1 :=
      (rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff
        B physical.1.1).2 hphysicalCrossAmbient
    exact hnoPair ⟨physical, hsourceCross, hphysicalCross⟩
  · exact Or.inl htarget


theorem rlc_twoChannelFullPhysical_staticCutTargetFailure_of_noPair
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1) :
    ¬∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧
        rlc_connectorOnLeft gamma' y ∧
          (rlc_twoChannelFullPhysicalCutTargetGraphAt
            gamma gamma' A).Reachable x y := by
  rintro ⟨x, y, hx, hy, ⟨w⟩⟩
  obtain ⟨p, q, hpq, hpB, hqB⟩ :=
    rlc_walk_pred_first_exit w (fun z => z ∈ B)
      (hBright x hx) (hBleft y hy)
  obtain ⟨target, htarget, u, v, hsource, hcrossA⟩ :=
    w.adj_of_mem_edges hpq
  apply hnoPair
  refine ⟨target, ⟨u, v, hsource, hcrossA⟩, ?_⟩
  exact ⟨p, q, htarget, Or.inl ⟨hpB, hqB⟩⟩


theorem
    rlc_bookFaithful_noPair_axisAnchorFirstNoncarrier_to_oppositeB
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
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1) :
    ∃ (f g z u v : Site 2)
      (w : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig
            gamma gamma' A))).Walk f z)
      (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A)).Walk f u)
      (r : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig
            gamma gamma' A))).Walk v z)
      (huv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig
            gamma gamma' A))).Adj u v),
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig
            gamma gamma' A)).Adj f g ∧
        (rlc_dualReflect z ∈ rlc_pathVertices gamma.1 ∨
          rlc_dualReflect z ∈ rlc_pathVertices gamma'.1) ∧
        ¬(rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔
          rlc_dualReflect z ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) ∧
        (rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔
          rlc_dualReflect u ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) ∧
        ¬(rlc_dualReflect u ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔
          rlc_dualReflect z ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' u v ∧
        w = (q.mapLe
          (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A))).append (.cons huv r) ∧
        s(u, v) ∈ w.edges ∧
        r.length < w.length := by
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
    rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
  obtain ⟨f, g, x, y, hanchor, hxPath, hyPath, ⟨wx⟩, ⟨wy⟩⟩ :=
    rlc_bookFaithful_fullFilledBoundary_axisAnchorPaths
      hfaith omega hno
  have extract {z : Site 2}
      (hzPath : rlc_dualReflect z ∈ rlc_pathVertices gamma.1 ∨
        rlc_dualReflect z ∈ rlc_pathVertices gamma'.1)
      (w : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk f z)
      (hcolor : ¬(rlc_dualReflect f ∈
          rlc_twoChannelFullPhysicalLiftVertexCut B ↔
        rlc_dualReflect z ∈
          rlc_twoChannelFullPhysicalLiftVertexCut B)) :
      ∃ (u v : Site 2)
        (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Walk f u)
        (r : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v z)
        (huv : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v),
        (rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔
          rlc_dualReflect u ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) ∧
        ¬(rlc_dualReflect u ∈
            rlc_twoChannelFullPhysicalLiftVertexCut B ↔
          rlc_dualReflect z ∈
            rlc_twoChannelFullPhysicalLiftVertexCut B) ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' u v ∧
        w = (q.mapLe
          (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma' omega)).append (.cons huv r) ∧
        s(u, v) ∈ w.edges ∧
        r.length < w.length := by
    rcases rlc_walk_subgraph_lift_or_first_exit_decomp
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma' omega) w with
      ⟨q, hq⟩ | ⟨u, v, q, r, huv, huvBad, hdecomp⟩
    · have hmono :=
        rlc_twoChannelFullPhysical_goodWalk_B_monochromatic_of_noPair
          gamma gamma' A B hAright hAleft hnoPair q
      exact False.elim (hcolor (by simpa [omega, hq] using hmono))
    · have hfu :=
        rlc_twoChannelFullPhysical_goodWalk_B_monochromatic_of_noPair
          gamma gamma' A B hAright hAleft hnoPair q
      have huz : ¬(rlc_dualReflect u ∈
          rlc_twoChannelFullPhysicalLiftVertexCut B ↔
        rlc_dualReflect z ∈
          rlc_twoChannelFullPhysicalLiftVertexCut B) := by
        intro huz
        exact hcolor (hfu.trans huz)
      have hbad :
          ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' u v := by
        intro hcarrier
        exact huvBad
          ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
            gamma gamma' omega).2 ⟨huv, hcarrier⟩)
      refine ⟨u, v, q, r, huv, hfu, huz, hbad, hdecomp, ?_, ?_⟩
      · rw [hdecomp]
        simp
      · rw [hdecomp]
        simp
        omega
  by_cases hfB : rlc_dualReflect f ∈
      rlc_twoChannelFullPhysicalLiftVertexCut B
  · have hyB : rlc_dualReflect y ∉
        rlc_twoChannelFullPhysicalLiftVertexCut B := by
      rintro ⟨hyBox, hyB⟩
      exact hBleft ⟨rlc_dualReflect y, hyBox⟩ hyPath hyB
    obtain ⟨u, v, q, r, huv, hfu, huz, hbad, hdecomp, hedge, hlen⟩ :=
      extract (Or.inr hyPath) wy (by simp [hfB, hyB])
    exact ⟨f, g, y, u, v, wy, q, r, huv, hanchor, Or.inr hyPath,
      by simp [hfB, hyB], hfu, huz, hbad, hdecomp, hedge, hlen⟩
  · have hxBox : rlc_dualReflect x ∈
        rect (-2 * n) (2 * n) (-n) n :=
      rlc_rightPathVertex_mem_connectorBox gamma hxPath
    have hxB : rlc_dualReflect x ∈
        rlc_twoChannelFullPhysicalLiftVertexCut B :=
      ⟨hxBox, hBright ⟨rlc_dualReflect x, hxBox⟩ hxPath⟩
    obtain ⟨u, v, q, r, huv, hfu, huz, hbad, hdecomp, hedge, hlen⟩ :=
      extract (Or.inl hxPath) wx (by simp [hfB, hxB])
    exact ⟨f, g, x, u, v, wx, q, r, huv, hanchor, Or.inl hxPath,
      by simp [hfB, hxB], hfu, huz, hbad, hdecomp, hedge, hlen⟩


theorem rlc_bookFaithful_staticCut_axisFullPhysicalPair
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
    ∃ (t : Int)
      (target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'),
      (gamma.1.1 : Site 2) 1 ≤ t ∧
        t + 1 ≤ (gamma'.1.2.1 : Site 2) 1 ∧
        target.1.1.map Subtype.val =
          s((![0, t] : Site 2), ![0, t + 1]) ∧
        (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val =
          s((![-1, t] : Site 2), ![0, t]) ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut A target.1.1 := by
  let ambientA := rlc_twoChannelFullPhysicalLiftVertexCut A
  have hAmbientRight : ∀ z ∈ rlc_pathVertices gamma.1, z ∈ ambientA := by
    intro z hz
    have hzBox : z ∈ rect (-2 * n) (2 * n) (-n) n :=
      rlc_rightPathVertex_mem_connectorBox gamma hz
    exact ⟨hzBox, hAright ⟨z, hzBox⟩ hz⟩
  have hAmbientLeft : ∀ z ∈ rlc_pathVertices gamma'.1, z ∉ ambientA := by
    intro z hz hzA
    obtain ⟨hzBox, hzA⟩ := hzA
    exact hAleft ⟨z, hzBox⟩ hz hzA
  obtain ⟨t, hbelow, habove, hcross, _htargetCarrier, _hsource⟩ :=
    rlc_bookFaithful_axisInterval_cutCrossing hfaith ambientA
      hAmbientRight hAmbientLeft
  obtain ⟨target, htarget⟩ :=
    rlc_bookFaithful_axisInterval_fullPhysicalTarget
      hfaith t hbelow habove
  have hsource :
      (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val =
        s((![-1, t] : Site 2), ![0, t]) := by
    calc
      _ = rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) :=
        rlc_twoChannelFullPhysicalSourceEdge_map target
      _ = rlc_pimsEdgeEquiv
          s((![0, t] : Site 2), ![0, t + 1]) := by rw [htarget]
      _ = _ := rlc_pimsEdgeEquiv_vertical 0 t
  refine ⟨t, target, hbelow, habove, htarget, hsource,
    (rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff
      A target.1.1).2 ?_⟩
  rwa [htarget]


theorem rlc_bookFaithful_staticCut_axisFullPhysicalTarget
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
    ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A target.1.1 := by
  obtain ⟨_t, target, _hbelow, _habove, _htarget, _hsource, hcross⟩ :=
    rlc_bookFaithful_staticCut_axisFullPhysicalPair
      hfaith A hAright hAleft
  exact ⟨target, hcross⟩


theorem RlcBookFaithfulTracePair.doubledAxisContact_geometry
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    let f := rlc_dualReflect.symm (gamma.1.1 : Site 2)
    let g := rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)
    StatMech.TwoDim.zfe_faceEmb f 0 = -1 ∧
      StatMech.TwoDim.zfe_faceEmb g 0 = -1 ∧
      StatMech.TwoDim.zfe_faceEmb f 1 <
        StatMech.TwoDim.zfe_faceEmb g 1 := by
  dsimp
  have hf0 : (gamma.1.1 : Site 2) 0 = 0 := gamma.1.1.2.2
  have hg0 : (gamma'.1.2.1 : Site 2) 0 = 0 := gamma'.1.2.1.2.2
  have hheight := hfaith.axis_contacts_strict
  simp only [StatMech.TwoDim.zfe_faceEmb, Matrix.cons_val_zero,
    Matrix.cons_val_one, rlc_dualReflect_symm_zero,
    rlc_dualReflect_symm_one]
  omega


theorem RlcBookFaithfulTracePair.dualFace_rightContact_position
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f : Site 2}
    (hf : rlc_dualReflect f ∈ rlc_pathVertices gamma.1) :
    (f 0 = -1 ∧ f 1 < -1) ∨ f 0 < -1 := by
  by_cases haxis : rlc_dualReflect f = (gamma.1.1 : Site 2)
  · left
    have h0 := congrArg (fun z : Site 2 => z 0) haxis
    have h1 := congrArg (fun z : Site 2 => z 1) haxis
    have hzero : ((gamma.1.1 : Site 2) 0) = 0 := gamma.1.1.2.2
    have hstrict := hfaith.toRlcBookPositionedTracePair.right_axis_strict
    simp [rlc_dualReflect, rlc_dualReflectFun] at h0 h1
    constructor <;> omega
  · right
    have hstrict := hfaith.right_vertex_strict hf haxis
    simp [rlc_dualReflect, rlc_dualReflectFun] at hstrict
    omega


theorem RlcBookFaithfulTracePair.dualFace_rightContact_axisColumn
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f : Site 2}
    (hf : rlc_dualReflect f ∈ rlc_pathVertices gamma.1)
    (hf0 : f 0 = -1) :
    f 1 < -1 := by
  rcases hfaith.dualFace_rightContact_position hf with haxis | hleft
  · exact haxis.2
  · omega


theorem RlcBookFaithfulTracePair.dualFace_leftContact_position
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f : Site 2}
    (hf : rlc_dualReflect f ∈ rlc_pathVertices gamma'.1) :
    (f 0 = -1 ∧ 0 ≤ f 1) ∨ 0 ≤ f 0 := by
  by_cases haxis : rlc_dualReflect f = (gamma'.1.2.1 : Site 2)
  · left
    have h0 := congrArg (fun z : Site 2 => z 0) haxis
    have h1 := congrArg (fun z : Site 2 => z 1) haxis
    have hzero : ((gamma'.1.2.1 : Site 2) 0) = 0 := gamma'.1.2.1.2.2
    have hstrict := hfaith.toRlcBookPositionedTracePair.left_axis_strict
    simp [rlc_dualReflect, rlc_dualReflectFun] at h0 h1
    constructor <;> omega
  · right
    have hstrict := hfaith.left_vertex_strict hf haxis
    simp [rlc_dualReflect, rlc_dualReflectFun] at hstrict
    omega


theorem RlcBookFaithfulTracePair.dualFace_leftContact_axisColumn
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f : Site 2}
    (hf : rlc_dualReflect f ∈ rlc_pathVertices gamma'.1)
    (hf0 : f 0 = -1) :
    0 ≤ f 1 := by
  rcases hfaith.dualFace_leftContact_position hf with haxis | hright
  · exact haxis.2
  · omega


theorem rlc_twoChannelFullPhysicalTargetCarrierGeometry_centralCarrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {S : Set (Site 2)}
    {f g : Site 2} (hfg : (faceBoundaryGraph S).Adj f g)
    (htarget : RlcTwoChannelFullPhysicalTargetCarrierGeometry
      gamma gamma' f g) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
  obtain ⟨hf, hg, htwo⟩ :=
    (rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local
      gamma gamma' f g).1 htarget
  have hclosure : (rlc_connectorCentralFaceClosureGraph gamma gamma').Adj
      ⟨rlc_dualReflect f, hf⟩ ⟨rlc_dualReflect g, hg⟩ := by
    rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
    exact Or.inl htwo
  apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' hfg.1).2
  simpa using hclosure.2


theorem rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginal
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {S : Set (Site 2)}
    {f g : Site 2} (hfg : (faceBoundaryGraph S).Adj f g)
    (hfRight : rlc_dualReflect f ∉ rlc_pathVertices gamma.1)
    (hfLeft : rlc_dualReflect f ∉ rlc_pathVertices gamma'.1)
    (hcentral : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' f g) :
    RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g := by
  have hplanar : s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma' :=
    (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hfg.1).1 hcentral
  have hfBox : rlc_dualReflect f ∈ rlc_connectorBox n :=
    rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hplanar (Sym2.mem_mk_left _ _)
  have hgBox : rlc_dualReflect g ∈ rlc_connectorBox n :=
    rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hplanar (Sym2.mem_mk_right _ _)
  have hfRect : rlc_dualReflect f ∈
      rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using hfBox
  have hgRect : rlc_dualReflect g ∈
      rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using hgBox
  let fs : RlcConnectorVertex n := ⟨rlc_dualReflect f, hfRect⟩
  let gs : RlcConnectorVertex n := ⟨rlc_dualReflect g, hgRect⟩
  have hclosure : (rlc_connectorCentralFaceClosureGraph
      gamma gamma').Adj fs gs := by
    exact ⟨(rlc_adj_dualReflect f g).mp hfg.1,
      by simpa [fs, gs] using hplanar⟩
  rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
    at hclosure
  rcases hclosure with htwo | htrace
  · exact (rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local
      gamma gamma' f g).2 ⟨hfRect, hgRect, htwo⟩
  · rcases Finset.mem_union.mp htrace.2 with hright | hleft
    · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1
        (by simpa [fs, gs] using hright)
      exact False.elim (hfRight hends.1)
    · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1
        (by simpa [fs, gs] using hleft)
      exact False.elim (hfLeft hends.1)


theorem
    rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginalEdge
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {S : Set (Site 2)}
    {f g : Site 2} (hfg : (faceBoundaryGraph S).Adj f g)
    (hnotOriginal : s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
    (hcentral : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' f g) :
    RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g := by
  have hplanar : s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma' :=
    (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hfg.1).1 hcentral
  have hfBox : rlc_dualReflect f ∈ rlc_connectorBox n :=
    rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hplanar (Sym2.mem_mk_left _ _)
  have hgBox : rlc_dualReflect g ∈ rlc_connectorBox n :=
    rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hplanar (Sym2.mem_mk_right _ _)
  have hfRect : rlc_dualReflect f ∈
      rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using hfBox
  have hgRect : rlc_dualReflect g ∈
      rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using hgBox
  let fs : RlcConnectorVertex n := ⟨rlc_dualReflect f, hfRect⟩
  let gs : RlcConnectorVertex n := ⟨rlc_dualReflect g, hgRect⟩
  have hclosure : (rlc_connectorCentralFaceClosureGraph
      gamma gamma').Adj fs gs := by
    exact ⟨(rlc_adj_dualReflect f g).mp hfg.1,
      by simpa [fs, gs] using hplanar⟩
  rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
    at hclosure
  rcases hclosure with htwo | htrace
  · exact (rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local
      gamma gamma' f g).2 ⟨hfRect, hgRect, htwo⟩
  · exact False.elim (hnotOriginal (by simpa [fs, gs] using htrace.2))


theorem rlc_twoChannelFullPhysical_nonopposite_targetContinuation
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {a u v : Site 2}
    (hau : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Adj a u)
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hav : a ≠ v)
    (huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1)
    (huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1)
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n)
    (hnotWall : s(rlc_dualReflect a, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hnonopposite : ¬((rlc_dualReflect a) 0 +
          (rlc_dualReflect v) 0 = 2 * (rlc_dualReflect u) 0 ∧
        (rlc_dualReflect a) 1 + (rlc_dualReflect v) 1 =
          2 * (rlc_dualReflect u) 1)) :
    RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v := by
  have hauTarget :=
    ((rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
      gamma gamma' a u).1
      ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).1 hau |>.2)).1
  have hauCentral :=
    rlc_twoChannelFullPhysicalTargetCarrierGeometry_centralCarrier
      gamma gamma' hau.1 hauTarget
  rcases hauCentral with hinWall | ⟨_haBox, _huBox, h, hhRegion, hhFlank⟩
  · exact False.elim (hnotWall hinWall)
  · apply rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginal
      gamma gamma' huv huRight huLeft
    apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' huv.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident
      gamma gamma'
        ((rlc_adj_dualReflect a u).mp hau.1.1).symm
        ((rlc_adj_dualReflect u v).mp huv.1)
    · intro heq
      exact hav (rlc_dualReflect.injective heq)
    · exact hnonopposite
    · exact huInterior
    · simpa [Sym2.eq_swap] using hnotWall
    · exact hhRegion
    · simpa [flankFaces_comm] using hhFlank


theorem rlc_twoChannelFullPhysical_exclusiveReflected_targetBad_allWall_or_opposite
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u v : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hbad : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
      gamma gamma' u v)
    (huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1)
    (huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1)
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n) :
    (∀ a : Site 2,
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Adj a u →
      a ≠ v →
      s(rlc_dualReflect a, rlc_dualReflect u) ∈
        rlc_connectorFourTraceEdges gamma gamma') ∨
      ∃ a : Site 2,
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Adj a u ∧
        a ≠ v ∧
        s(rlc_dualReflect a, rlc_dualReflect u) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        ((rlc_dualReflect a) 0 + (rlc_dualReflect v) 0 =
            2 * (rlc_dualReflect u) 0 ∧
          (rlc_dualReflect a) 1 + (rlc_dualReflect v) 1 =
            2 * (rlc_dualReflect u) 1) := by
  by_cases hex : ∃ a : Site 2,
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Adj a u ∧
      a ≠ v ∧
      s(rlc_dualReflect a, rlc_dualReflect u) ∉
        rlc_connectorFourTraceEdges gamma gamma'
  · obtain ⟨a, hau, hav, hnotWall⟩ := hex
    by_cases hopp : (rlc_dualReflect a) 0 + (rlc_dualReflect v) 0 =
          2 * (rlc_dualReflect u) 0 ∧
        (rlc_dualReflect a) 1 + (rlc_dualReflect v) 1 =
          2 * (rlc_dualReflect u) 1
    · exact Or.inr ⟨a, hau, hav, hnotWall, hopp⟩
    · exact False.elim (hbad
        (rlc_twoChannelFullPhysical_nonopposite_targetContinuation
          hau huv hav huRight huLeft huInterior hnotWall hopp))
  · left
    intro a hau hav
    by_contra hnotWall
    exact hex ⟨a, hau, hav, hnotWall⟩


theorem rlc_twoChannelFullPhysical_goodWalk_end_dualReflect_mem_box
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x y)
    (hxBox : rlc_dualReflect x ∈ rlc_connectorBox n) :
    rlc_dualReflect y ∈ rlc_connectorBox n := by
  induction q with
  | nil => exact hxBox
  | @cons a b c hab q ih =>
      have hcarrier :=
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).1 hab).2
      have htarget :=
        ((rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
          gamma gamma' a b).1 hcarrier).1
      obtain ⟨_ha, hb, _hab⟩ :=
        (rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local
          gamma gamma' a b).1 htarget
      exact ih (by simpa [rlc_connectorBox] using hb)


theorem rlc_twoChannelFullPhysical_targetBad_near_mem_barrier_of_interior
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x u v : Site 2}
    (hxBarrier : rlc_dualReflect x ∈
      rlc_connectorBarrier gamma gamma')
    (hxBox : rlc_dualReflect x ∈ rlc_connectorBox n)
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hbadTarget : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
      gamma gamma' u v)
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n) :
    rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
  by_contra huBarrier
  have hincident : ∃ w : Site 2,
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Adj u w := by
    by_cases hux : u = x
    · subst u
      exact False.elim (huBarrier hxBarrier)
    · obtain ⟨p⟩ := q.reachable.symm
      cases p with
      | nil => exact False.elim (hux rfl)
      | @cons a w c haw p => exact ⟨w, haw⟩
  obtain ⟨w, huwGood⟩ := hincident
  have huwBoundary := huwGood.1
  have huwCentral : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u w :=
    rlc_twoChannelFullPhysicalTargetCarrierGeometry_centralCarrier
      gamma gamma' huwBoundary
      (((rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
        gamma gamma' u w).1
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).1 huwGood |>.2)).1)
  rcases huwCentral with huwWall | ⟨_huBox, hwBox, h, hhRegion, hhFlank⟩
  · exact huBarrier (rlc_mem_connectorBarrier_of_mem_fourTraceEdge
      gamma gamma' huwWall (Sym2.mem_mk_left _ _))
  · have huBox :=
      rlc_twoChannelFullPhysical_goodWalk_end_dualReflect_mem_box q hxBox
    have huvTarget : (hypercubicLattice 2).Adj
        (rlc_dualReflect u) (rlc_dualReflect v) :=
      (rlc_adj_dualReflect u v).mp huv.1
    have huwTarget : (hypercubicLattice 2).Adj
        (rlc_dualReflect u) (rlc_dualReflect w) :=
      (rlc_adj_dualReflect u w).mp huwBoundary.1
    have hvBox : rlc_dualReflect v ∈ rlc_connectorBox n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
      rw [mem_rect]
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at huvTarget
      omega
    have hnotWall : s(rlc_dualReflect u, rlc_dualReflect v) ∉
        rlc_connectorFourTraceEdges gamma gamma' := by
      intro hwall
      exact huBarrier (rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' hwall (Sym2.mem_mk_left _ _))
    generalize hkEq : flankFaces
      (rlc_dualReflect u) (rlc_dualReflect v) = e
    induction e using Sym2.inductionOn with
    | _ k l =>
        have hkFlank : k ∈ flankFaces
            (rlc_dualReflect u) (rlc_dualReflect v) := by
          rw [hkEq]
          exact Sym2.mem_mk_left _ _
        have hkRegion := rlc_centralFaceRegion_flank_transfer_interior
          gamma gamma' huwTarget huvTarget huInterior huBarrier
            hhRegion hhFlank hkFlank
        have hclosure : s(rlc_dualReflect u, rlc_dualReflect v) ∈
            rlc_connectorCentralFaceClosureEdges gamma gamma' :=
          (rlc_mem_connectorCentralFaceClosureEdges_iff
            gamma gamma' huvTarget).2
              ⟨huBox, hvBox, k, hkRegion, hkFlank⟩
        have huRect : rlc_dualReflect u ∈
            rect (-2 * n) (2 * n) (-n) n := by
          simpa [rlc_connectorBox] using huBox
        have hvRect : rlc_dualReflect v ∈
            rect (-2 * n) (2 * n) (-n) n := by
          simpa [rlc_connectorBox] using hvBox
        have hcentral : (rlc_connectorCentralFaceFiniteGraph
            gamma gamma').Adj
              ⟨rlc_dualReflect u, huRect⟩ ⟨rlc_dualReflect v, hvRect⟩ :=
          ⟨huvTarget, Finset.mem_sdiff.mpr ⟨hclosure, hnotWall⟩⟩
        have htwo := rlc_connectorCentralFaceFiniteGraph_le_twoChannel
          gamma gamma' hcentral
        apply hbadTarget
        exact (rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local
          gamma gamma' u v).2 ⟨huRect, hvRect, htwo⟩


theorem rlc_twoChannelFullPhysical_targetBad_near_barrier_or_boxBoundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x u v : Site 2}
    (hxBarrier : rlc_dualReflect x ∈
      rlc_connectorBarrier gamma gamma')
    (hxBox : rlc_dualReflect x ∈ rlc_connectorBox n)
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hbadTarget : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
      gamma gamma' u v) :
    rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨
      (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n := by
  have huBox :=
    rlc_twoChannelFullPhysical_goodWalk_end_dualReflect_mem_box q hxBox
  by_cases huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n
  · exact Or.inl
      (rlc_twoChannelFullPhysical_targetBad_near_mem_barrier_of_interior
        hxBarrier hxBox q huv hbadTarget huInterior)
  · right
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
    rw [mem_rect] at huBox
    push Not at huInterior
    omega


theorem rlc_twoChannelFull_reflectedLeft_hit_sourceNE_not_filled
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {u w : Site 2} (hw : w ∈ rlc_pathVertices gamma'.1)
    (hu : rlc_dualReflect u = rlc_flipX w) :
    (![u 0 + 1, u 1 + 1] : Site 2) ∉
      rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
  have hcorner : (![u 0 + 1, u 1 + 1] : Site 2) = w := by
    have h0 := congrArg (fun z : Site 2 => z 0) hu
    have h1 := congrArg (fun z : Site 2 => z 1) hu
    ext i
    fin_cases i <;>
      simp [rlc_dualReflect, rlc_dualReflectFun,
        rlc_flipX, rlc_flipXFun] at h0 h1 ⊢ <;>
      omega
  rw [hcorner]
  have hwExt := rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
    gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hw
  simpa only [rlc_twoChannelFullFilledReachSet,
    Set.mem_compl_iff, not_not] using hwExt


theorem rlc_twoChannelFull_reflectedRight_hit_sourceNE_mem_filled
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u w : Site 2} (hw : w ∈ rlc_pathVertices gamma.1)
    (hu : rlc_dualReflect u = rlc_flipX w) :
    (![u 0 + 1, u 1 + 1] : Site 2) ∈
      rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
  have hcorner : (![u 0 + 1, u 1 + 1] : Site 2) = w := by
    have h0 := congrArg (fun z : Site 2 => z 0) hu
    have h1 := congrArg (fun z : Site 2 => z 1) hu
    ext i
    fin_cases i <;>
      simp [rlc_dualReflect, rlc_dualReflectFun,
        rlc_flipX, rlc_flipXFun] at h0 h1 ⊢ <;>
      omega
  rw [hcorner]
  exact rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
    (rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega hw)


theorem rlc_twoChannelFullFilledBoundary_preimage_not_exposed
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
    sharedPrimalEdge f g ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  have hclosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      (sharedPrimalEdge f g) = false := by
    have hopen := rlc_twoChannelFullFilledBoundary_le_openFaceDual
      gamma gamma' omega hfg
    rw [openSubgraph_adj] at hopen
    have h := hopen.2
    rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1] at h
    simpa using h
  intro htrace
  have hopen := rlc_twoChannelFullAmbientConfig_trace
    gamma gamma' omega htrace
  rw [hclosed] at hopen
  contradiction


theorem rlc_twoChannelFull_reflectedHit_boundary_step_ne_right_of_south_exposed
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u v w : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hu : rlc_dualReflect u = rlc_flipX w)
    (hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    v ≠ ![u 0 + 1, u 1] := by
  intro hv
  subst v
  exact (rlc_twoChannelFullFilledBoundary_preimage_not_exposed
    gamma gamma' omega huv)
      ((rlc_reflectedHit_sharedPrimalEdge_right hu).symm ▸ hsouth)


theorem rlc_twoChannelFull_reflectedHit_boundary_step_ne_top_of_west_exposed
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u v w : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hu : rlc_dualReflect u = rlc_flipX w)
    (hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    v ≠ ![u 0, u 1 + 1] := by
  intro hv
  subst v
  exact (rlc_twoChannelFullFilledBoundary_preimage_not_exposed
    gamma gamma' omega huv)
      ((rlc_reflectedHit_sharedPrimalEdge_top hu).symm ▸ hwest)

theorem rlc_twoChannelFull_reflectedLeft_opposite_continuation_centralCarrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma'.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect v = rlc_flipX r)
    (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' hvb.1).2
  let x := rlc_dualReflect v
  let a := rlc_dualReflect u
  let c := rlc_dualReflect b
  have hxa : (hypercubicLattice 2).Adj x a :=
    (rlc_adj_dualReflect u v).mp huv.1 |>.symm
  have hxc : (hypercubicLattice 2).Adj x c :=
    (rlc_adj_dualReflect v b).mp hvb.1
  have hac : a ≠ c := by
    intro hac
    apply hub
    apply rlc_dualReflect.injective
    exact hac
  have sideTransfer (y : Site 2)
      (hxy : (hypercubicLattice 2).Adj x y)
      (hya : y ≠ a) (hyc : y ≠ c)
      (hay : ¬ (a 0 + y 0 = 2 * x 0 ∧ a 1 + y 1 = 2 * x 1))
      (hycOpp : ¬ (y 0 + c 0 = 2 * x 0 ∧ y 1 + c 1 = 2 * x 1))
      (hnot : s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma') :
      s(x, c) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
    exact rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side
      gamma gamma' hxa hxc hvInterior hnotIn hhRegion hh
        ⟨y, hxy, hya, hyc, hay, hycOpp, hnot⟩
  have hpreNot :=
    rlc_twoChannelFullFilledBoundary_preimage_not_exposed
      gamma gamma' omega huv
  rcases face_adj_dir hxa with ha | ha | ha | ha
  · have hc : c = ![x 0 - 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have hb : b = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0 + 1, v 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_twoChannelFullFilledBoundary_preimage_not_exposed
            gamma gamma' omega hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_right _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0 + 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have huSource : u = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0 + 1, v 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_right _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0, x 1 - 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have huSource : u = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0, v 1 + 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_right _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl
  · have hc : c = ![x 0, x 1 + 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have hb : b = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0, v 1 + 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [c, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_twoChannelFullFilledBoundary_preimage_not_exposed
            gamma gamma' omega hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_right _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl


theorem rlc_twoChannelFull_reflectedLeft_opposite_continuation_targetCarrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma'.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect v = rlc_flipX r)
    (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' v b := by
  apply rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginal
    gamma gamma' hvb hvRight hvLeft
  exact rlc_twoChannelFull_reflectedLeft_opposite_continuation_centralCarrier
    gamma gamma' omega huv hvb hub hvflip hw hvRight hvLeft hvFlipRight
      hopp hvInterior hnotIn hhRegion hh

theorem rlc_twoChannelFull_reflectedRight_opposite_continuation_centralCarrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect v = rlc_flipX r)
    (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' hvb.1).2
  let x := rlc_dualReflect v
  let a := rlc_dualReflect u
  let c := rlc_dualReflect b
  have hxa : (hypercubicLattice 2).Adj x a :=
    (rlc_adj_dualReflect u v).mp huv.1 |>.symm
  have hxc : (hypercubicLattice 2).Adj x c :=
    (rlc_adj_dualReflect v b).mp hvb.1
  have hac : a ≠ c := by
    intro hac
    apply hub
    apply rlc_dualReflect.injective
    exact hac
  have sideTransfer (y : Site 2)
      (hxy : (hypercubicLattice 2).Adj x y)
      (hya : y ≠ a) (hyc : y ≠ c)
      (hay : ¬ (a 0 + y 0 = 2 * x 0 ∧ a 1 + y 1 = 2 * x 1))
      (hycOpp : ¬ (y 0 + c 0 = 2 * x 0 ∧ y 1 + c 1 = 2 * x 1))
      (hnot : s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma') :
      s(x, c) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
    exact rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side
      gamma gamma' hxa hxc hvInterior hnotIn hhRegion hh
        ⟨y, hxy, hya, hyc, hay, hycOpp, hnot⟩
  have hpreNot :=
    rlc_twoChannelFullFilledBoundary_preimage_not_exposed
      gamma gamma' omega huv
  rcases face_adj_dir hxa with ha | ha | ha | ha
  · have hc : c = ![x 0 - 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have hb : b = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0 + 1, v 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_twoChannelFullFilledBoundary_preimage_not_exposed
            gamma gamma' omega hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_left _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0 + 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have huSource : u = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0 + 1, v 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_left _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0, x 1 - 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have huSource : u = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0, v 1 + 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_left _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl
  · have hc : c = ![x 0, x 1 + 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have hb : b = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0, v 1 + 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [c, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_twoChannelFullFilledBoundary_preimage_not_exposed
            gamma gamma' omega hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_left _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl


theorem rlc_twoChannelFull_reflectedRight_opposite_continuation_targetCarrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect v = rlc_flipX r)
    (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' v b := by
  apply rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginal
    gamma gamma' hvb hvRight hvLeft
  exact rlc_twoChannelFull_reflectedRight_opposite_continuation_centralCarrier
    gamma gamma' omega huv hvb hub hvflip hw hvRight hvLeft hvFlipLeft
      hopp hvInterior hnotIn hhRegion hh


theorem rlc_twoChannelFullPhysical_interior_exclusiveReflected_targetBad_allWall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u v : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hbad : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
      gamma gamma' u v)
    (huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1)
    (huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1)
    (huReflected :
      (0 < (rlc_dualReflect u) 0 ∧
        ∃ w ∈ rlc_pathVertices gamma'.1,
          rlc_dualReflect u = rlc_flipX w) ∨
      ((rlc_dualReflect u) 0 < 0 ∧
        ∃ w ∈ rlc_pathVertices gamma.1,
          rlc_dualReflect u = rlc_flipX w))
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n) :
    ∀ a : Site 2,
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Adj a u →
      a ≠ v →
      s(rlc_dualReflect a, rlc_dualReflect u) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
  rcases rlc_twoChannelFullPhysical_exclusiveReflected_targetBad_allWall_or_opposite
      huv hbad huRight huLeft huInterior with hall | hopposite
  · exact hall
  · obtain ⟨a, hau, hav, hnotWall, hopp⟩ := hopposite
    have hauTarget :=
      ((rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
        gamma gamma' a u).1
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).1 hau |>.2)).1
    have hauCentral :=
      rlc_twoChannelFullPhysicalTargetCarrierGeometry_centralCarrier
        gamma gamma' hau.1 hauTarget
    rcases hauCentral with hinWall | ⟨_haBox, _huBox, h, hhRegion, hhFlank⟩
    · exact False.elim (hnotWall hinWall)
    · rcases huReflected with ⟨huPos, w, hw, hflip⟩ |
          ⟨huNeg, w, hw, hflip⟩
      · have hflipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1,
            rlc_dualReflect u = rlc_flipX r := by
          rintro ⟨r, hr, heq⟩
          have hrRect := rlc_pathVertex_mem_rect gamma.1 hr
          rw [mem_rect] at hrRect
          have huPos' := huPos
          rw [heq] at huPos'
          simp [rlc_flipX, rlc_flipXFun] at huPos'
          omega
        exact False.elim (hbad
          (rlc_twoChannelFull_reflectedLeft_opposite_continuation_targetCarrier
            gamma gamma' omega hau.1 huv hav hflip hw huRight huLeft
              hflipRight hopp huInterior
              (by simpa [Sym2.eq_swap] using hnotWall)
              hhRegion (by simpa [flankFaces_comm] using hhFlank)))
      · have hflipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1,
            rlc_dualReflect u = rlc_flipX r := by
          rintro ⟨r, hr, heq⟩
          have hrRect := rlc_pathVertex_mem_rect gamma'.1 hr
          rw [mem_rect] at hrRect
          have huNeg' := huNeg
          rw [heq] at huNeg'
          simp [rlc_flipX, rlc_flipXFun] at huNeg'
          omega
        exact False.elim (hbad
          (rlc_twoChannelFull_reflectedRight_opposite_continuation_targetCarrier
            gamma gamma' omega hau.1 huv hav hflip hw huRight huLeft
              hflipLeft hopp huInterior
              (by simpa [Sym2.eq_swap] using hnotWall)
              hhRegion (by simpa [flankFaces_comm] using hhFlank)))


end
end StatMech.Universality
