/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part92
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_traceSplitCounterexample_not_filledBoundaryTargetSupported :
    ¬ RlcConnectorPIMSFilledBoundaryTargetSupported
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
      rlc_traceSplitCounterexampleFiniteAllClosed := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let tau := rlc_traceSplitCounterexampleFiniteAllClosed
  let omega := rlc_connectorAmbientMixedConfig gamma gamma' tau
  let K := rlc_connectorReachSet gamma gamma' omega
  let H := rlc_connectorFilledReachSet gamma gamma' omega
  have hpPath : (![2, 0] : Site 2) ∈ rlc_pathVertices gamma.1 := by
    rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
      rlc_traceSplitCounterexample_right_vertices]
    simp
  have hpK : (![2, 0] : Site 2) ∈ K :=
    rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hpPath
  have hpH : (![2, 0] : Site 2) ∈ H :=
    rlc_connectorReachSet_subset_filled gamma gamma' omega hpK
  have hKbox : K ⊆ box 2 2 := by
    intro z hz
    have hzRect := rlc_connectorReachSet_subset_box gamma gamma' omega hz
    rw [mem_box]
    intro i
    fin_cases i <;> simp [mem_rect] at hzRect ⊢ <;> omega
  have hqExtBox : (![3, 0] : Site 2) ∈ exterior 2 2 := by
    rw [exterior_eq_compl_box, Set.mem_compl_iff, mem_box]
    simp
  have hqNotK : (![3, 0] : Site 2) ∈ Kᶜ :=
    exterior_subset_compl K 2 hKbox hqExtBox
  have hqInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨![3, 0], hqNotK⟩).supp.Infinite :=
    exterior_mem_infiniteComponent (by norm_num) K 2 hKbox hqExtBox
  have hqComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨![3, 0], hqNotK⟩ =
        rlc_connectorExteriorComponent gamma gamma' omega :=
    (unique_infinite_component (by norm_num) K
      (rlc_connectorReachSet_finite gamma gamma' omega)).unique hqInf
        (rlc_connectorExteriorComponent_infinite gamma gamma' omega)
  have hqExterior : (![3, 0] : Site 2) ∈
      rlc_connectorExteriorSet gamma gamma' omega := ⟨hqNotK, hqComp⟩
  have hqH : (![3, 0] : Site 2) ∉ H := by
    exact fun h => h hqExterior
  have hboundary : (faceBoundaryGraph H).Adj
      (![2, 0] : Site 2) ![2, -1] := by
    exact faceBoundaryGraph_adj_vert H 2 0 (iff_of_true hpH hqH)
  intro htarget
  have hedge : s((![-3, 1] : Site 2), ![-3, 0]) ∈
      rlc_connectorEdges gamma gamma' := by
    simpa [H, K, omega, tau, gamma, gamma', rlc_dualReflect,
      rlc_dualReflectFun] using htarget hboundary
  have hbox := rlc_connectorEdge_endpoint_mem_box gamma gamma' hedge
    (Sym2.mem_mk_left (![-3, 1] : Site 2) ![-3, 0])
  simp [mem_rect] at hbox


theorem rlc_traceSplitCounterexample_finiteAllClosed_reachSet_eq :
    rlc_connectorReachSet rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft
        (rlc_connectorAmbientMixedConfig rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft
          rlc_traceSplitCounterexampleFiniteAllClosed) =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)) := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let tau := rlc_traceSplitCounterexampleFiniteAllClosed
  let omega := rlc_connectorAmbientMixedConfig gamma gamma' tau
  have hmask : rlc_maskConfig (rlc_connectorEdges gamma gamma') omega =
      (fun _ => false) := by
    funext e
    by_cases he : e ∈ rlc_connectorEdges gamma gamma'
    · simp [rlc_maskConfig, he, omega, tau,
        rlc_traceSplitCounterexampleFiniteAllClosed]
    · simp [rlc_maskConfig, he]
  apply Set.Subset.antisymm
  · rintro z ⟨hzBox, x, hxPath, hxBox, hxz⟩
    have hopen : openSubgraphInduce 2
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
        (rect (-2 : Int) 2 (-1) 1) = ⊥ := by
      ext u v
      simp [openSubgraphInduce_adj, hmask]
    have hxz' : ConnectedWithin 2
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
        (rect (-2 : Int) 2 (-1) 1)
        ⟨x, by simpa using hxBox⟩ ⟨z, by simpa using hzBox⟩ := by
      simpa [gamma, gamma', omega] using hxz
    change (openSubgraphInduce 2
      (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (rect (-2 : Int) 2 (-1) 1)).Reachable _ _ at hxz'
    rw [hopen] at hxz'
    have hxEq : x = z := congrArg Subtype.val
      (SimpleGraph.reachable_bot.mp hxz')
    simpa [gamma, hxEq] using hxPath
  · intro z hz
    exact rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega
      (by simpa [gamma] using hz)


theorem rlc_traceSplitCounterexample_finiteAllClosed_boundaryArc :
    RlcConnectorPIMSBoundaryArc rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft
      rlc_traceSplitCounterexampleFiniteAllClosed := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let tau := rlc_traceSplitCounterexampleFiniteAllClosed
  let omega := rlc_connectorAmbientMixedConfig gamma gamma' tau
  let K := rlc_connectorReachSet gamma gamma' omega
  have hK : K =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)) :=
    rlc_traceSplitCounterexample_finiteAllClosed_reachSet_eq
  have h01 : (faceBoundaryGraph K).Adj
      (![-1, -2] : Site 2) ![-1, -1] := by
    apply (faceBoundaryGraph_adj_vert K (-1) (-1) ?_).symm
    rw [hK, rlc_traceSplitCounterexample_right_vertices]
    simp
  have h12 : (faceBoundaryGraph K).Adj
      (![-1, -1] : Site 2) ![0, -1] := by
    apply (faceBoundaryGraph_adj_horiz K 0 (-1) ?_).symm
    rw [hK, rlc_traceSplitCounterexample_right_vertices]
    simp
  have h23 : (faceBoundaryGraph K).Adj
      (![0, -1] : Site 2) ![1, -1] := by
    apply (faceBoundaryGraph_adj_horiz K 1 (-1) ?_).symm
    rw [hK, rlc_traceSplitCounterexample_right_vertices]
    simp
  let a : (faceBoundaryGraph K).Walk
      (![-1, -2] : Site 2) ![1, -1] :=
    .cons h01 (.cons h12 (.cons h23 .nil))
  have hOrigin : (origin 2) ∈ rlc_connectorOriginRegion gamma gamma' := by
    rw [rlc_connectorOriginRegion]
    simp only [Set.Finite.mem_toFinset]
    have ho : origin 2 ∈ rlc_connectorAllowed gamma gamma' := by
      rw [rlc_connectorAllowed, Finset.mem_sdiff]
      constructor
      · simp [rlc_connectorBox, mem_rect, origin]
      · rw [show origin 2 = (![0, 0] : Site 2) by
          ext i
          fin_cases i <;> rfl]
        rw [rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices,
          rlc_traceSplitCounterexample_left_vertices]
        simp [rlc_flipX, rlc_flipXFun]
    exact ⟨ho, ho, Reachable.refl _⟩
  have hMinus : (![-1, 0] : Site 2) ∈
      rlc_connectorOriginRegion gamma gamma' := by
    have hOne : (![1, 0] : Site 2) ∈
        rlc_connectorOriginRegion gamma gamma' := by
      simpa [gamma, gamma'] using
        rlc_extremalSelection_one_zero_mem_originRegion
    have hflip := (rlc_connectorOriginRegion_mem_flipX_iff
      gamma gamma' (![1, 0] : Site 2)).mp hOne
    simpa [rlc_flipX, rlc_flipXFun] using hflip
  have he01 : s((![0, -1] : Site 2), ![0, 0]) ∈
      rlc_connectorEdges gamma gamma' := by
    rw [rlc_connectorEdges, Finset.mem_filter]
    constructor
    · rw [mem_edgesWithinFinset]
      exact ⟨![0, -1], by simp [rlc_connectorBox, mem_rect],
        ![0, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩
    · refine ⟨origin 2, hOrigin, ?_⟩
      rw [show origin 2 = (![0, 0] : Site 2) by
        ext i
        fin_cases i <;> rfl]
      exact Sym2.mem_mk_right (![0, -1] : Site 2) ![0, 0]
  have he12 : s((![0, 0] : Site 2), ![-1, 0]) ∈
      rlc_connectorEdges gamma gamma' := by
    rw [rlc_connectorEdges, Finset.mem_filter]
    constructor
    · rw [mem_edgesWithinFinset]
      exact ⟨![0, 0], by simp [rlc_connectorBox, mem_rect],
        ![-1, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩
    · exact ⟨![-1, 0], hMinus,
        Sym2.mem_mk_right (![0, 0] : Site 2) ![-1, 0]⟩
  have he23 : s((![-1, 0] : Site 2), ![-2, 0]) ∈
      rlc_connectorEdges gamma gamma' := by
    rw [rlc_connectorEdges, Finset.mem_filter]
    constructor
    · rw [mem_edgesWithinFinset]
      exact ⟨![-1, 0], by simp [rlc_connectorBox, mem_rect],
        ![-2, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩
    · exact ⟨![-1, 0], hMinus,
        Sym2.mem_mk_left (![-1, 0] : Site 2) ![-2, 0]⟩
  refine ⟨![-1, -2], ![1, -1], a, ?_, ?_, ?_⟩
  · rw [rlc_traceSplitCounterexample_right_vertices]
    simp [rlc_dualReflect, rlc_dualReflectFun]
  · rw [rlc_traceSplitCounterexample_left_vertices]
    simp [rlc_dualReflect, rlc_dualReflectFun]
  · dsimp only
    let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma') omega
    let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma' omega
    intro e he
    have hEdges : (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges =
        (a.mapLe hle).edges.map
          (Sym2.map (rlc_dualReflectOpenHom eta)) :=
      SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (a.mapLe hle)
    rw [hEdges] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    have heA : e0 ∈ a.edges := by
      rwa [SimpleGraph.Walk.edges_mapLe_eq_edges] at he0
    simp only [a, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_nil, List.mem_cons, List.not_mem_nil,
      or_false] at heA
    rcases heA with rfl | rfl | rfl
    · simpa [eta, rlc_dualReflectOpenHom, Sym2.map_mk,
        rlc_dualReflect, rlc_dualReflectFun] using he01
    · simpa [eta, rlc_dualReflectOpenHom, Sym2.map_mk,
        rlc_dualReflect, rlc_dualReflectFun] using he12
    · simpa [eta, rlc_dualReflectOpenHom, Sym2.map_mk,
        rlc_dualReflect, rlc_dualReflectFun] using he23


theorem rlc_traceSplitCounterexample_finiteAllClosed_failure :
    rlc_traceSplitCounterexampleFiniteAllClosed ∉
      rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let tau := rlc_traceSplitCounterexampleFiniteAllClosed
  have hopen : FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau = ⊥ := by
    ext x y
    simp [FK.openSub_adj, tau,
      rlc_traceSplitCounterexampleFiniteAllClosed]
  have hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
      rlc_traceSplitCounterexample_right_vertices] at hz
    rw [show gamma' = rlc_traceSplitCounterexampleLeft by rfl,
      rlc_traceSplitCounterexample_left_vertices] at hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  rintro ⟨x, y, hx, hy, hxy⟩
  rw [hopen] at hxy
  have hxyEq : x = y := SimpleGraph.reachable_bot.mp hxy
  subst y
  exact Finset.disjoint_left.mp hdisj hx hy


theorem rlc_traceSplitCounterexample_reflectedDual_failure :
    rlc_connectorReflectedDualConfig rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft
        rlc_traceSplitCounterexampleFiniteAllClosed ∉
      rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let tau := rlc_traceSplitCounterexampleFiniteAllClosed
  let rho := rlc_connectorReflectedDualConfig gamma gamma' tau
  have hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
      rlc_traceSplitCounterexample_right_vertices] at hz
    rw [show gamma' = rlc_traceSplitCounterexampleLeft by rfl,
      rlc_traceSplitCounterexample_left_vertices] at hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  have hsourceNot {e : Sym2 (Site 2)}
      (hall : ∀ z ∈ e, z ∈ rlc_connectorBarrier gamma gamma') :
      e ∉ rlc_connectorEdges gamma gamma' := by
    intro he
    rw [rlc_connectorEdges, Finset.mem_filter] at he
    obtain ⟨z, hzRegion, hze⟩ := he.2
    exact rlc_originRegion_not_barrier hzRegion (hall z hze)
  have hrightIsolated (x y : RlcConnectorVertex 1)
      (hx : rlc_connectorOnRight gamma x)
      (hxy : (FK.openSub (rlc_connectorFiniteGraph gamma gamma') rho).Adj x y) :
      False := by
    rw [FK.openSub_adj] at hxy
    have hpre : rlc_pimsEdgeEquiv s((x : Site 2), (y : Site 2)) ∈
        rlc_connectorEdges gamma gamma' := by
      exact rlc_connectorReflectedDualConfig_open_preimage_mem_connector
        gamma gamma' tau s(x, y) (by simpa [rho, Sym2.map_mk] using hxy.2)
    have hxBarrier : (x : Site 2) ∈ rlc_connectorBarrier gamma gamma' := by
      simp only [rlc_connectorBarrier, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl hx))
    have htargetEdge := hxy.1.2
    rw [rlc_connectorEdges, Finset.mem_filter] at htargetEdge
    obtain ⟨z, hzRegion, hzEdge⟩ := htargetEdge.2
    have hyRegion : (y : Site 2) ∈
        rlc_connectorOriginRegion gamma gamma' := by
      rw [Sym2.mem_iff] at hzEdge
      rcases hzEdge with hz | hz
      · subst z
        exact False.elim (rlc_originRegion_not_barrier hzRegion hxBarrier)
      · simpa [hz] using hzRegion
    have hySet : (y : Site 2) ∈
        rlc_connectorOriginRegionSet gamma gamma' := by
      simpa [rlc_connectorOriginRegion] using hyRegion
    obtain ⟨hyAllowed, _ho, _hreach⟩ := hySet
    have hyBox : (y : Site 2) ∈ rlc_connectorBox 1 :=
      (Finset.mem_sdiff.mp hyAllowed).1
    have hyNotBarrier : (y : Site 2) ∉
        rlc_connectorBarrier gamma gamma' :=
      (Finset.mem_sdiff.mp hyAllowed).2
    have htarget :
        s((x : Site 2), (y : Site 2)) =
            s((![0, -1] : Site 2), ![0, 0]) ∨
          s((x : Site 2), (y : Site 2)) =
            s((![1, -1] : Site 2), ![1, 0]) ∨
          s((x : Site 2), (y : Site 2)) =
            s((![2, 0] : Site 2), ![1, 0]) := by
      change (x : Site 2) ∈ rlc_pathVertices gamma.1 at hx
      rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
        rlc_traceSplitCounterexample_right_vertices] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx | hx <;>
        (have hx0 := congrArg (fun z : Site 2 => z 0) hx
         have hx1 := congrArg (fun z : Site 2 => z 1) hx
         simp at hx0 hx1
         have hadj := hxy.1.1
         rw [hx] at hadj
         rcases adj_cases hadj with
          ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩ <;>
           simp at h0 h1)
      · have hyEq : (y : Site 2) = ![0, -2] := by
          ext i
          fin_cases i <;> simp <;> omega
        rw [hyEq, rlc_connectorBox] at hyBox
        simp [mem_rect] at hyBox
      · left
        congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
      · have hyEq : (y : Site 2) = ![-1, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp [rlc_flipX, rlc_flipXFun]
      · have hyEq : (y : Site 2) = ![1, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![1, -2] := by
          ext i
          fin_cases i <;> simp <;> omega
        rw [hyEq, rlc_connectorBox] at hyBox
        simp [mem_rect] at hyBox
      · right; left
        congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
      · have hyEq : (y : Site 2) = ![0, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![2, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![2, -2] := by
          ext i
          fin_cases i <;> simp <;> omega
        rw [hyEq, rlc_connectorBox] at hyBox
        simp [mem_rect] at hyBox
      · have hyEq : (y : Site 2) = ![2, 0] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![1, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![3, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        rw [hyEq, rlc_connectorBox] at hyBox
        simp [mem_rect] at hyBox
      · have hyEq : (y : Site 2) = ![2, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![2, 1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_left_vertices]
        simp [rlc_flipX, rlc_flipXFun]
      · right; right
        congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
      · have hyEq : (y : Site 2) = ![3, 0] := by
          ext i
          fin_cases i <;> simp <;> omega
        rw [hyEq, rlc_connectorBox] at hyBox
        simp [mem_rect] at hyBox
    rcases htarget with ht | ht | ht
    · have hs : s((![-1, -1] : Site 2), ![0, -1]) ∈
          rlc_connectorEdges gamma gamma' := by
        have hpims : rlc_pimsEdgeEquiv
            s((![0, -1] : Site 2), ![0, 0]) =
              s((![-1, -1] : Site 2), ![0, -1]) := by
          simpa using rlc_pimsEdgeEquiv_vertical 0 (-1)
        rw [ht, hpims] at hpre
        simpa using hpre
      exact hsourceNot (e := s((![-1, -1] : Site 2), ![0, -1])) (by
        intro z hz
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl <;>
          rw [rlc_connectorBarrier,
            rlc_traceSplitCounterexample_right_vertices] <;>
          simp [rlc_flipX, rlc_flipXFun]) hs
    · have hs : s((![-2, -1] : Site 2), ![-1, -1]) ∈
          rlc_connectorEdges gamma gamma' := by
        have hpims : rlc_pimsEdgeEquiv
            s((![1, -1] : Site 2), ![1, 0]) =
              s((![-2, -1] : Site 2), ![-1, -1]) := by
          simpa using rlc_pimsEdgeEquiv_vertical 1 (-1)
        rw [ht, hpims] at hpre
        simpa using hpre
      exact hsourceNot (e := s((![-2, -1] : Site 2), ![-1, -1])) (by
        intro z hz
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl <;>
          rw [rlc_connectorBarrier,
            rlc_traceSplitCounterexample_right_vertices] <;>
          simp [rlc_flipX, rlc_flipXFun]) hs
    · have hs : s((![-2, -1] : Site 2), ![-2, 0]) ∈
          rlc_connectorEdges gamma gamma' := by
        have hpims : rlc_pimsEdgeEquiv
            s((![1, 0] : Site 2), ![2, 0]) =
              s((![-2, -1] : Site 2), ![-2, 0]) := by
          simpa using rlc_pimsEdgeEquiv_horizontal 1 0
        rw [ht, show s((![2, 0] : Site 2), ![1, 0]) =
          s((![1, 0] : Site 2), ![2, 0]) from Sym2.eq_swap,
          hpims] at hpre
        simpa using hpre
      exact hsourceNot (e := s((![-2, -1] : Site 2), ![-2, 0])) (by
        intro z hz
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · rw [rlc_connectorBarrier,
            rlc_traceSplitCounterexample_right_vertices]
          simp [rlc_flipX, rlc_flipXFun]
        · rw [rlc_connectorBarrier,
            rlc_traceSplitCounterexample_left_vertices]
          simp) hs
  rintro ⟨x, y, hx, hy, hxy⟩
  obtain ⟨w⟩ := hxy
  cases w with
  | nil =>
      exact Finset.disjoint_left.mp hdisj hx hy
  | cons h _ => exact hrightIsolated x _ hx h


theorem rlc_connectorPIMSBoundaryArc_of_filledBoundary {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcontacts : RlcConnectorPIMSFilledBoundaryContacts gamma gamma' tau)
    (htarget : RlcConnectorPIMSFilledBoundaryTargetSupported gamma gamma' tau) :
    RlcConnectorPIMSBoundaryArc gamma gamma' tau := by
  obtain ⟨x, y, hxSupp, hySupp, hxPath, hyPath⟩ := hcontacts
  let omega := rlc_connectorAmbientMixedConfig gamma gamma' tau
  obtain ⟨p⟩ := rlc_connectorFilledFaceBoundary_reachable
    gamma gamma' omega hxSupp hySupp
  let hfill :=
    rlc_connectorFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
      gamma gamma' omega
  let a := p.mapLe hfill
  refine ⟨x, y, a, hxPath, hyPath, ?_⟩
  dsimp only
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma') omega
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma' omega
  intro e he
  have hEdges : (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges =
      (a.mapLe hle).edges.map
        (Sym2.map (rlc_dualReflectOpenHom eta)) :=
    SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (a.mapLe hle)
  rw [hEdges] at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  induction e0 using Sym2.inductionOn with
  | _ f g =>
      have hfgA : s(f, g) ∈ a.edges := by
        rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at he0
        exact he0
      have hfgP : s(f, g) ∈ p.edges := by
        dsimp only [a] at hfgA
        rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hfgA
        exact hfgA
      change s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_connectorEdges gamma gamma'
      exact htarget (p.adj_of_mem_edges hfgP)


end
end StatMech.Universality
