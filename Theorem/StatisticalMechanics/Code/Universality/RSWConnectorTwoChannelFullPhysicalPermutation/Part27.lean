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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part27
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_targetBad_prefix_allWall_or_terminalWallRun
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x u v : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
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
    (∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma') ∨
      RlcTwoChannelFullPhysicalTerminalWallRunAt gamma gamma' omega q := by
  let P : Sym2 (Site 2) → Prop := fun e =>
    Sym2.map rlc_dualReflect e ∈
      rlc_connectorFourTraceEdges gamma gamma'
  rcases rlc_walk_all_edges_or_last_failure_decomp P q with hall |
      ⟨a, b, p, r, hab, hnotWall, hrWall, hdecomp⟩
  · exact Or.inl hall
  · right
    have hallIncoming :=
      rlc_twoChannelFullPhysical_interior_exclusiveReflected_targetBad_allWall
        huv hbad huRight huLeft huReflected huInterior
    have hrNotNil : ¬r.Nil := by
      intro hrNil
      have hbu : b = u := hrNil.eq
      subst b
      have hav : a ≠ v := by
        intro hav
        subst a
        have hgood : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
            gamma gamma' omega).Adj u v := hab.symm
        have hcarrier :=
          ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
            gamma gamma' omega).1 hgood).2
        exact hbad
          ((rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
            gamma gamma' u v).1 hcarrier).1
      have hauWall := hallIncoming a hab hav
      apply hnotWall
      simpa [P, Sym2.map_mk] using hauWall
    exact ⟨a, b, p, r, hab,
      by simpa [P, Sym2.map_mk] using hnotWall,
      hrWall, hrNotNil, hdecomp⟩


theorem RlcBookFaithfulTracePair.reflectedTraceVertices_disjoint
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z : Site 2}
    (hzRight : ∃ r ∈ rlc_pathVertices gamma.1, z = rlc_flipX r)
    (hzLeft : ∃ l ∈ rlc_pathVertices gamma'.1, z = rlc_flipX l) : False := by
  obtain ⟨r, hr, rfl⟩ := hzRight
  obtain ⟨l, hl, hrl⟩ := hzLeft
  have hrl' : r = l := by
    apply rlc_flipX.injective
    simpa using hrl
  subst l
  have hrRect := rlc_pathVertex_mem_rect gamma.1 hr
  have hlRect := rlc_pathVertex_mem_rect gamma'.1 hl
  rw [mem_rect] at hrRect hlRect
  have hr0 : r 0 = 0 := by omega
  have hrStart := hfaith.right_axis_unique hr hr0
  have hlEnd := hfaith.left_axis_unique hl hr0
  have hrow := congrArg (fun x : Site 2 => x 1) (hrStart.symm.trans hlEnd)
  exact (ne_of_lt hfaith.axis_contacts_strict) hrow


theorem RlcBookFaithfulTracePair.traceVertices_disjoint
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : z ∈ rlc_pathVertices gamma'.1) : False := by
  have hrRect := rlc_pathVertex_mem_rect gamma.1 hzRight
  have hlRect := rlc_pathVertex_mem_rect gamma'.1 hzLeft
  rw [mem_rect] at hrRect hlRect
  have hz0 : z 0 = 0 := by omega
  have hrStart := hfaith.right_axis_unique hzRight hz0
  have hlEnd := hfaith.left_axis_unique hzLeft hz0
  have hrow := congrArg (fun x : Site 2 => x 1) (hrStart.symm.trans hlEnd)
  exact (ne_of_lt hfaith.axis_contacts_strict) hrow


theorem rlc_twoChannelFullPhysical_goodWallTarget_reflected
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {f g : Site 2}
    (hfg : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Adj f g)
    (hwall : s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorFourTraceEdges gamma gamma') :
    s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_reflectedPathEdges gamma.1 ∨
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_reflectedPathEdges gamma'.1 := by
  have htarget :=
    ((rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
      gamma gamma' f g).1
      ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).1 hfg |>.2)).1
  obtain ⟨hf, hg, htwo⟩ :=
    (rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local
      gamma gamma' f g).1 htarget
  have hnotOriginal : s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
    intro horiginal
    exact htwo.2 ⟨(rlc_adj_dualReflect f g).mp hfg.1.1, horiginal⟩
  rw [rlc_connectorFourTraceEdges, Finset.mem_union] at hwall
  rcases hwall with horiginal | hreflected
  · exact False.elim (hnotOriginal horiginal)
  · simpa [rlc_connectorReflectedTraceEdges] using hreflected


theorem rlc_twoChannelFullPhysical_goodWallWalk_oneReflectedFamily
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x y)
    (hall : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma') :
    q.Nil ∨
      (∀ e ∈ q.edges,
        Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) ∨
      (∀ e ∈ q.edges,
        Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) := by
  have propagateRight : ∀ {a b : Site 2}
      (w : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk a b),
      (∃ r ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect a = rlc_flipX r) →
      (∀ e ∈ w.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') →
      ∀ e ∈ w.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_reflectedPathEdges gamma.1 := by
    intro a b w ha hwall
    induction w with
    | nil => simp
    | @cons a c b hac p ih =>
        have hacWall : s(rlc_dualReflect a, rlc_dualReflect c) ∈
            rlc_connectorFourTraceEdges gamma gamma' := by
          simpa [Sym2.map_mk] using hwall s(a, c) (by simp)
        have hacRight : s(rlc_dualReflect a, rlc_dualReflect c) ∈
            rlc_reflectedPathEdges gamma.1 := by
          rcases rlc_twoChannelFullPhysical_goodWallTarget_reflected
              hac hacWall with hright | hleft
          · exact hright
          · have haLeft := rlc_reflectedPathEdge_endpoint_mem_vertices
              gamma'.1 hleft (Sym2.mem_mk_left _ _)
            exact False.elim
              (hfaith.reflectedTraceVertices_disjoint ha haLeft)
        have hcRight := rlc_reflectedPathEdge_endpoint_mem_vertices
          gamma.1 hacRight (Sym2.mem_mk_right _ _)
        have hpWall : ∀ e ∈ p.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
          intro e he
          exact hwall e (by simp [he])
        intro e he
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
        rcases he with rfl | he
        · simpa [Sym2.map_mk] using hacRight
        · exact ih hcRight hpWall e he
  have propagateLeft : ∀ {a b : Site 2}
      (w : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk a b),
      (∃ l ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect a = rlc_flipX l) →
      (∀ e ∈ w.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') →
      ∀ e ∈ w.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_reflectedPathEdges gamma'.1 := by
    intro a b w ha hwall
    induction w with
    | nil => simp
    | @cons a c b hac p ih =>
        have hacWall : s(rlc_dualReflect a, rlc_dualReflect c) ∈
            rlc_connectorFourTraceEdges gamma gamma' := by
          simpa [Sym2.map_mk] using hwall s(a, c) (by simp)
        have hacLeft : s(rlc_dualReflect a, rlc_dualReflect c) ∈
            rlc_reflectedPathEdges gamma'.1 := by
          rcases rlc_twoChannelFullPhysical_goodWallTarget_reflected
              hac hacWall with hright | hleft
          · have haRight := rlc_reflectedPathEdge_endpoint_mem_vertices
              gamma.1 hright (Sym2.mem_mk_left _ _)
            exact False.elim
              (hfaith.reflectedTraceVertices_disjoint haRight ha)
          · exact hleft
        have hcLeft := rlc_reflectedPathEdge_endpoint_mem_vertices
          gamma'.1 hacLeft (Sym2.mem_mk_right _ _)
        have hpWall : ∀ e ∈ p.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
          intro e he
          exact hwall e (by simp [he])
        intro e he
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
        rcases he with rfl | he
        · simpa [Sym2.map_mk] using hacLeft
        · exact ih hcLeft hpWall e he
  by_cases hnil : q.Nil
  · exact Or.inl hnil
  · have hfirst := q.mk_start_snd_mem_edges hnil
    have hfirstWall : s(rlc_dualReflect x, rlc_dualReflect q.snd) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      simpa [Sym2.map_mk] using hall s(x, q.snd) hfirst
    rcases rlc_twoChannelFullPhysical_goodWallTarget_reflected
        (q.adj_of_mem_edges hfirst) hfirstWall with hright | hleft
    · have hxRight := rlc_reflectedPathEdge_endpoint_mem_vertices
        gamma.1 hright (Sym2.mem_mk_left _ _)
      exact Or.inr (Or.inl (propagateRight q hxRight hall))
    · have hxLeft := rlc_reflectedPathEdge_endpoint_mem_vertices
        gamma'.1 hleft (Sym2.mem_mk_left _ _)
      exact Or.inr (Or.inr (propagateLeft q hxLeft hall))

theorem rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x y)
    (hnotNil : ¬q.Nil)
    (hall : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma')
    (hyLeft : ∃ l ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect y = rlc_flipX l) :
    ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_reflectedPathEdges gamma'.1 := by
  rcases rlc_twoChannelFullPhysical_goodWallWalk_oneReflectedFamily
      hfaith q hall with hnil | hright | hleft
  · exact False.elim (hnotNil hnil)
  · have hlast := q.mk_penultimate_end_mem_edges hnotNil
    have hlastRight := hright _ hlast
    induction hedge : s(q.penultimate, y) using Sym2.inductionOn with
    | _ a b =>
        have hmap : Sym2.map rlc_dualReflect s(a, b) =
            s(rlc_dualReflect q.penultimate, rlc_dualReflect y) := by
          rw [← hedge]
          simp [Sym2.map_mk]
        have hyRight := rlc_reflectedPathEdge_endpoint_mem_vertices
          gamma.1 (by simpa [hedge, hmap] using hlastRight)
            (Sym2.mem_mk_right _ _)
        exact False.elim
          (hfaith.reflectedTraceVertices_disjoint hyRight hyLeft)
  · exact hleft

theorem rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x y)
    (hnotNil : ¬q.Nil)
    (hall : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma')
    (hyRight : ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect y = rlc_flipX r) :
    ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_reflectedPathEdges gamma.1 := by
  rcases rlc_twoChannelFullPhysical_goodWallWalk_oneReflectedFamily
      hfaith q hall with hnil | hright | hleft
  · exact False.elim (hnotNil hnil)
  · exact hright
  · have hlast := q.mk_penultimate_end_mem_edges hnotNil
    have hlastLeft := hleft _ hlast
    induction hedge : s(q.penultimate, y) using Sym2.inductionOn with
    | _ a b =>
        have hmap : Sym2.map rlc_dualReflect s(a, b) =
            s(rlc_dualReflect q.penultimate, rlc_dualReflect y) := by
          rw [← hedge]
          simp [Sym2.map_mk]
        have hyLeft := rlc_reflectedPathEdge_endpoint_mem_vertices
          gamma'.1 (by simpa [hedge, hmap] using hlastLeft)
            (Sym2.mem_mk_right _ _)
        exact False.elim
          (hfaith.reflectedTraceVertices_disjoint hyRight hyLeft)


theorem rlc_twoChannelFullPhysical_reflectedLeftWalk_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x y)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (hy : ∃ l ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect y = rlc_flipX l) :
    ∃ l ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect x = rlc_flipX l := by
  by_cases hnil : q.Nil
  · simpa [hnil.eq] using hy
  · have hfirst := q.mk_start_snd_mem_edges hnil
    have hfirstLeft : s(rlc_dualReflect x,
        rlc_dualReflect q.snd) ∈ rlc_reflectedPathEdges gamma'.1 := by
      simpa [Sym2.map_mk] using hedges s(x, q.snd) hfirst
    exact rlc_reflectedPathEdge_endpoint_mem_vertices
      gamma'.1 hfirstLeft (Sym2.mem_mk_left _ _)


theorem rlc_twoChannelFullPhysical_reflectedRightWalk_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x y)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (hy : ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect y = rlc_flipX r) :
    ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect x = rlc_flipX r := by
  by_cases hnil : q.Nil
  · simpa [hnil.eq] using hy
  · have hfirst := q.mk_start_snd_mem_edges hnil
    have hfirstRight : s(rlc_dualReflect x,
        rlc_dualReflect q.snd) ∈ rlc_reflectedPathEdges gamma.1 := by
      simpa [Sym2.map_mk] using hedges s(x, q.snd) hfirst
    exact rlc_reflectedPathEdge_endpoint_mem_vertices
      gamma.1 hfirstRight (Sym2.mem_mk_left _ _)


theorem rlc_twoChannelFullPhysical_orderedRightContact_reflectedLeft_start_eq
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x y)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hfirst : ∀ w ∈ right.support,
      rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (hy : ∃ l ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect y = rlc_flipX l) :
    rlc_dualReflect x = z := by
  have hxRight : rlc_dualReflect x ∈ right.support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hxOrder
    obtain ⟨w, hw, hwx⟩ := hxOrder
    change rlc_flipX w = rlc_flipX (rlc_dualReflect x) at hwx
    have heq : w = rlc_dualReflect x := rlc_flipX.injective hwx
    simpa [heq] using hw
  obtain ⟨l, hl, hxl⟩ :=
    rlc_twoChannelFullPhysical_reflectedLeftWalk_start q hedges hy
  apply hfirst (rlc_dualReflect x) hxRight
  rw [hxl]
  simpa using hl


theorem rlc_twoChannelFullPhysical_rightContact_reflectedRight_start_eq_axis
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x y)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (hy : ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect y = rlc_flipX r) :
    rlc_dualReflect x = (gamma.1.1 : Site 2) := by
  obtain ⟨r, hr, hxr⟩ :=
    rlc_twoChannelFullPhysical_reflectedRightWalk_start q hedges hy
  by_contra hxAxis
  have hxPos := hfaith.right_vertex_strict hxPath hxAxis
  by_cases hrAxis : r = (gamma.1.1 : Site 2)
  · apply hxAxis
    rw [hxr, hrAxis]
    exact rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  have hrPos := hfaith.right_vertex_strict hr hrAxis
  rw [hxr] at hxPos
  change 0 < -r 0 at hxPos
  omega


theorem rlc_twoChannelFullPhysical_leftContact_reflectedLeft_start_eq_axis
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x y)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma'.1)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (hy : ∃ l ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect y = rlc_flipX l) :
    rlc_dualReflect x = (gamma'.1.2.1 : Site 2) := by
  obtain ⟨l, hl, hxl⟩ :=
    rlc_twoChannelFullPhysical_reflectedLeftWalk_start q hedges hy
  by_contra hxAxis
  have hxNeg := hfaith.left_vertex_strict hxPath hxAxis
  by_cases hlAxis : l = (gamma'.1.2.1 : Site 2)
  · apply hxAxis
    rw [hxl, hlAxis]
    exact rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hlNeg := hfaith.left_vertex_strict hl hlAxis
  rw [hxl] at hxNeg
  change -l 0 < 0 at hxNeg
  omega


theorem rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_suffix_at
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    (z : Site 2)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    {c u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk c u)
    (hcEnd : rlc_dualReflect c = (gamma'.1.2.1 : Site 2))
    (hqReflectedLeft : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) :
    ∃ (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support),
      rlc_dualReflect u ∈
        (((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).dropUntil z hz).support := by
  let W := (rlc_ambientCrossingWalk gamma'.1).map
    rlc_flipXLatticeHom
  have hflipZWL : rlc_flipX z ∈
      (rlc_ambientCrossingWalk gamma'.1).support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzLeft
  have hzW : z ∈ W.support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨rlc_flipX z, hflipZWL, rlc_flipX_involutive z⟩
  let hDual :
      rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let qDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect c) (rlc_dualReflect u) := q.map hDual
  have hqDualEdges : ∀ e ∈ qDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (q.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 (hqReflectedLeft e0 he0)
  have hcPath : rlc_dualReflect c ∈ rlc_pathVertices gamma'.1 := by
    rw [hcEnd]
    exact rlc_connector_path_end_mem_vertices gamma'.1
  have hqDualAvoid : z ∉ qDual.support := by
    intro hzq
    change z ∈ (q.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨x, hxQ, hxz⟩ := hzq
    change rlc_dualReflect x = z at hxz
    have hxRight : rlc_dualReflect x ∈
        rlc_pathVertices gamma.1 := by simpa [hxz] using hzRight
    exact (rlc_twoChannelFullPhysical_noGood_leftWalk_end_not_rightContact
      hnoGood hcPath (q.takeUntil x hxQ)) hxRight
  have hupperFlip : rlc_flipX (gamma'.1.2.1 : Site 2) =
      (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hcInSuffix : rlc_dualReflect c ∈
      (W.dropUntil z hzW).support := by
    rw [hcEnd]
    have hend : rlc_flipX (gamma'.1.2.1 : Site 2) ∈
        (W.dropUntil z hzW).support :=
      (W.dropUntil z hzW).end_mem_support
    rw [hupperFlip] at hend
    exact hend
  have huSuffix := rlc_walk_end_mem_pathSuffix_of_avoid
    W (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
      hzW qDual hcInSuffix hqDualEdges hqDualAvoid
  exact ⟨hzW, huSuffix⟩


theorem rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_suffix_at
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    (z : Site 2)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    {c u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk c u)
    (hcStart : rlc_dualReflect c = (gamma.1.1 : Site 2))
    (hqReflectedRight : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) :
    ∃ (hz : rlc_flipX z ∈
        (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support),
      rlc_dualReflect u ∈
        ((((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).dropUntil
            (rlc_flipX z) hz).support := by
  have hzWR : z ∈ (rlc_ambientCrossingWalk gamma.1).support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2
      hzRight
  let W := ((rlc_ambientCrossingWalk gamma.1).map
    rlc_flipXLatticeHom).reverse
  have hzMapped : rlc_flipX z ∈
      ((rlc_ambientCrossingWalk gamma.1).map
        rlc_flipXLatticeHom).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨z, hzWR, rfl⟩
  have hzW : rlc_flipX z ∈ W.support := by
    simpa [W, SimpleGraph.Walk.support_reverse] using hzMapped
  let hDual :
      rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let qDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect c) (rlc_dualReflect u) := q.map hDual
  have hqDualEdges : ∀ e ∈ qDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (q.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    have hforward :=
      rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
        gamma.1 (hqReflectedRight e0 he0)
    simpa [W, SimpleGraph.Walk.edges_reverse] using hforward
  have hcPath : rlc_dualReflect c ∈ rlc_pathVertices gamma.1 := by
    rw [hcStart]
    exact rlc_path_start_mem_vertices gamma.1
  have hqDualAvoid : rlc_flipX z ∉ qDual.support := by
    intro hzq
    change rlc_flipX z ∈ (q.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨x, hxQ, hxz⟩ := hzq
    change rlc_dualReflect x = rlc_flipX z at hxz
    have hxLeft : rlc_dualReflect x ∈
        rlc_pathVertices gamma'.1 := by simpa [hxz] using hzLeft
    exact (rlc_twoChannelFullPhysical_noGood_rightWalk_end_not_leftContact
      hnoGood hcPath (q.takeUntil x hxQ)) hxLeft
  have hlowerFlip : rlc_flipX (gamma.1.1 : Site 2) =
      (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  have hcInSuffix : rlc_dualReflect c ∈
      (W.dropUntil (rlc_flipX z) hzW).support := by
    rw [hcStart]
    have hend : rlc_flipX (gamma.1.1 : Site 2) ∈
        (W.dropUntil (rlc_flipX z) hzW).support :=
      (W.dropUntil (rlc_flipX z) hzW).end_mem_support
    rw [hlowerFlip] at hend
    exact hend
  have huSuffix := rlc_walk_end_mem_pathSuffix_of_avoid
    W ((rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse)
      hzW qDual hcInSuffix hqDualEdges hqDualAvoid
  exact ⟨hzW, huSuffix⟩


theorem rlc_twoChannelFullPhysical_leftContact_terminalReflectedLeft_sameSide_at
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    (z : Site 2)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    {x u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
    (hxLeft : rlc_dualReflect x ∈ rlc_pathVertices gamma'.1)
    (hrun : RlcTwoChannelFullPhysicalTerminalWallRunAt
      gamma gamma' omega q)
    (huLeft : ∃ l ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect u = rlc_flipX l) :
    ∃ (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support)
      (b : Site 2),
      rlc_dualReflect b ∈
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support ∧
        rlc_dualReflect u ∈
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support ∧
        (rlc_dualReflect b ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support ↔
          rlc_dualReflect u ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support) := by
  obtain ⟨a, b, p, r, hab, _hnonwall, hrWall, hrNotNil, hdecomp⟩ := hrun
  have hrLeft :=
    rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal
      hfaith r hrNotNil hrWall huLeft
  let W := (rlc_ambientCrossingWalk gamma'.1).map
    rlc_flipXLatticeHom
  have hflipZWL : rlc_flipX z ∈
      (rlc_ambientCrossingWalk gamma'.1).support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzLeft
  have hzW : z ∈ W.support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨rlc_flipX z, hflipZWL, rlc_flipX_involutive z⟩
  let hDual :
      rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let rDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect b) (rlc_dualReflect u) := r.map hDual
  have hrDualEdges : ∀ e ∈ rDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (r.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 (hrLeft e0 he0)
  have hrSupportQ : ∀ w ∈ r.support, w ∈ q.support := by
    intro w hw
    rw [hdecomp, SimpleGraph.Walk.mem_support_append_iff]
    right
    simp [hw]
  have hrDualAvoid : z ∉ rDual.support := by
    intro hzq
    change z ∈ (r.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨w, hwR, hwz⟩ := hzq
    change rlc_dualReflect w = z at hwz
    have hwRight : rlc_dualReflect w ∈
        rlc_pathVertices gamma.1 := by simpa [hwz] using hzRight
    exact (rlc_twoChannelFullPhysical_noGood_leftWalk_end_not_rightContact
      hnoGood hxLeft (q.takeUntil w (hrSupportQ w hwR))) hwRight
  have hfirstEdge := r.mk_start_snd_mem_edges hrNotNil
  have hfirstMapped : s(rlc_dualReflect b,
      rlc_dualReflect r.snd) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect b, rlc_dualReflect r.snd) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      exact ⟨s(b, r.snd), hfirstEdge, rfl⟩)
  have hbW := W.fst_mem_support_of_mem_edges hfirstMapped
  have hlastEdge := r.mk_penultimate_end_mem_edges hrNotNil
  have hlastMapped : s(rlc_dualReflect r.penultimate,
      rlc_dualReflect u) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect r.penultimate, rlc_dualReflect u) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      exact ⟨s(r.penultimate, u), hlastEdge, rfl⟩)
  have huW := W.snd_mem_support_of_mem_edges hlastMapped
  have hsame := rlc_walk_end_mem_pathSuffix_iff_of_avoid
    W (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
      hzW rDual hrDualEdges hrDualAvoid
  exact ⟨hzW, b, hbW, huW, hsame⟩


theorem rlc_twoChannelFullPhysical_rightContact_terminalReflectedRight_sameSide_at
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    (z : Site 2)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    {x u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
    (hxRight : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hrun : RlcTwoChannelFullPhysicalTerminalWallRunAt
      gamma gamma' omega q)
    (huRight : ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX r) :
    ∃ (hz : rlc_flipX z ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support)
      (b : Site 2),
      rlc_dualReflect b ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support ∧
        rlc_dualReflect u ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support ∧
        (rlc_dualReflect b ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support ↔
          rlc_dualReflect u ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support) := by
  obtain ⟨a, b, p, r, hab, _hnonwall, hrWall, hrNotNil, hdecomp⟩ := hrun
  have hrRight :=
    rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal
      hfaith r hrNotNil hrWall huRight
  let W := ((rlc_ambientCrossingWalk gamma.1).map
    rlc_flipXLatticeHom).reverse
  have hzWR : z ∈ (rlc_ambientCrossingWalk gamma.1).support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2
      hzRight
  have hzMapped : rlc_flipX z ∈
      ((rlc_ambientCrossingWalk gamma.1).map
        rlc_flipXLatticeHom).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨z, hzWR, rfl⟩
  have hzW : rlc_flipX z ∈ W.support := by
    simpa [W, SimpleGraph.Walk.support_reverse] using hzMapped
  let hDual :
      rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let rDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect b) (rlc_dualReflect u) := r.map hDual
  have hrDualEdges : ∀ e ∈ rDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (r.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    have hforward :=
      rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
        gamma.1 (hrRight e0 he0)
    simpa [W, SimpleGraph.Walk.edges_reverse] using hforward
  have hrSupportQ : ∀ w ∈ r.support, w ∈ q.support := by
    intro w hw
    rw [hdecomp, SimpleGraph.Walk.mem_support_append_iff]
    right
    simp [hw]
  have hrDualAvoid : rlc_flipX z ∉ rDual.support := by
    intro hzq
    change rlc_flipX z ∈ (r.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨w, hwR, hwz⟩ := hzq
    change rlc_dualReflect w = rlc_flipX z at hwz
    have hwLeft : rlc_dualReflect w ∈
        rlc_pathVertices gamma'.1 := by simpa [hwz] using hzLeft
    exact (rlc_twoChannelFullPhysical_noGood_rightWalk_end_not_leftContact
      hnoGood hxRight (q.takeUntil w (hrSupportQ w hwR))) hwLeft
  have hfirstEdge := r.mk_start_snd_mem_edges hrNotNil
  have hfirstMapped : s(rlc_dualReflect b,
      rlc_dualReflect r.snd) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect b, rlc_dualReflect r.snd) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      exact ⟨s(b, r.snd), hfirstEdge, rfl⟩)
  have hbW := W.fst_mem_support_of_mem_edges hfirstMapped
  have hlastEdge := r.mk_penultimate_end_mem_edges hrNotNil
  have hlastMapped : s(rlc_dualReflect r.penultimate,
      rlc_dualReflect u) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect r.penultimate, rlc_dualReflect u) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      exact ⟨s(r.penultimate, u), hlastEdge, rfl⟩)
  have huW := W.snd_mem_support_of_mem_edges hlastMapped
  have hsame := rlc_walk_end_mem_pathSuffix_iff_of_avoid
    W ((rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse)
      hzW rDual hrDualEdges hrDualAvoid
  exact ⟨hzW, b, hbW, huW, hsame⟩


theorem rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {c u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk c u)
    (hcEnd : rlc_dualReflect c = (gamma'.1.2.1 : Site 2))
    (hqReflectedLeft : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) :
    ∃ (z : Site 2)
      (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect u ∈
          (((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).dropUntil z hz).support := by
  obtain ⟨z, _hzWR, hzRight, hzLeft, _hfirst, _hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  obtain ⟨hz, hu⟩ :=
    rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_suffix_at
      hnoGood z hzRight hzLeft q hcEnd hqReflectedLeft
  exact ⟨z, hz, hzRight, hzLeft, hu⟩


theorem rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {c u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk c u)
    (hcStart : rlc_dualReflect c = (gamma.1.1 : Site 2))
    (hqReflectedRight : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) :
    ∃ (z : Site 2)
      (hz : rlc_flipX z ∈
        (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect u ∈
          ((((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).dropUntil
              (rlc_flipX z) hz).support := by
  obtain ⟨z, _hzWR, hzRight, hzLeft, _hfirst, _hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  obtain ⟨hz, hu⟩ :=
    rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_suffix_at
      hnoGood z hzRight hzLeft q hcStart hqReflectedRight
  exact ⟨z, hz, hzRight, hzLeft, hu⟩


theorem rlc_twoChannelFullPhysical_sourceCarrier_of_planar
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hplanar : sharedPrimalEdge f g ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma') :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g := by
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hclosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      (sharedPrimalEdge f g) = false := by
    have hopen := rlc_twoChannelFullFilledBoundary_le_openFaceDual
      gamma gamma' omega hfg
    rw [openSubgraph_adj] at hopen
    have h := hopen.2
    rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1] at h
    simpa using h
  have hpBox : p ∈ rlc_connectorBox n := by
    rw [hpq, rlc_mem_connectorCentralFacePlanarEdges_iff
      gamma gamma' hpqAdj] at hplanar
    rcases hplanar with hwall | hregion
    · simpa [rlc_connectorBox] using
        (rlc_connectorBarrier_mem_connectorBox gamma gamma'
          (rlc_mem_connectorBarrier_of_mem_fourTraceEdge
            gamma gamma' hwall (Sym2.mem_mk_left _ _)))
    · exact hregion.1
  have hqBox : q ∈ rlc_connectorBox n := by
    rw [hpq, rlc_mem_connectorCentralFacePlanarEdges_iff
      gamma gamma' hpqAdj] at hplanar
    rcases hplanar with hwall | hregion
    · simpa [rlc_connectorBox] using
        (rlc_connectorBarrier_mem_connectorBox gamma gamma'
          (rlc_mem_connectorBarrier_of_mem_fourTraceEdge
            gamma gamma' hwall (Sym2.mem_mk_right _ _)))
    · exact hregion.2.1
  have hpRect : p ∈ rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using hpBox
  have hqRect : q ∈ rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using hqBox
  let ps : RlcConnectorVertex n := ⟨p, hpRect⟩
  let qs : RlcConnectorVertex n := ⟨q, hqRect⟩
  have hclosure : (rlc_connectorCentralFaceClosureGraph
      gamma gamma').Adj ps qs := by
    exact ⟨hpqAdj, by simpa [ps, qs, hpq] using hplanar⟩
  rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace] at hclosure
  rcases hclosure with htwo | htrace
  · let source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
      ⟨s(ps, qs), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
    exact ⟨source, by
      simpa [source, ps, qs, Sym2.map_mk] using hpq.symm⟩
  · have hopen := rlc_twoChannelFullAmbientConfig_trace
      gamma gamma' omega htrace.2
    rw [← hpq, hclosed] at hopen
    contradiction


theorem rlc_twoChannelFullPhysical_sourceCarrier_planar
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {f g : Site 2}
    (hsource : RlcTwoChannelFullPhysicalSourceCarrierGeometry
      gamma gamma' f g) :
    sharedPrimalEdge f g ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  obtain ⟨source, hsourceMap⟩ := hsource
  induction hedge : source.1 using Sym2.inductionOn with
  | _ x y =>
      have htwo : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp (hedge ▸ source.2)
      have hclosure : (rlc_connectorCentralFaceClosureGraph
          gamma gamma').Adj x y := by
        rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
        exact Or.inl htwo
      rw [← hsourceMap]
      simpa [hedge, Sym2.map_mk] using hclosure.2


theorem rlc_twoChannelFullPhysical_sourceCarrier_iff_planar
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g ↔
      sharedPrimalEdge f g ∈
        rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  exact ⟨rlc_twoChannelFullPhysical_sourceCarrier_planar gamma gamma',
    rlc_twoChannelFullPhysical_sourceCarrier_of_planar
      gamma gamma' omega hfg⟩


theorem rlc_twoChannelFullPhysical_targetCarrier_iff_planar_of_nonoriginalEdge
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {S : Set (Site 2)}
    {f g : Site 2} (hfg : (faceBoundaryGraph S).Adj f g)
    (hnotOriginal : s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g ↔
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  constructor
  · intro htarget
    exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hfg.1).1
        (rlc_twoChannelFullPhysicalTargetCarrierGeometry_centralCarrier
          gamma gamma' hfg htarget)
  · intro hplanar
    apply
      rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginalEdge
        gamma gamma' hfg hnotOriginal
    exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hfg.1).2 hplanar


theorem
    rlc_twoChannelFullPhysical_noPair_BChanging_boundary_planar_obstruction
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
    sharedPrimalEdge f g ∉
        rlc_connectorCentralFacePlanarEdges gamma gamma' ∨
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_connectorCentralFacePlanarEdges gamma gamma' ∨
      rlc_dualReflect f ∈ rlc_pathVertices gamma.1 ∨
      rlc_dualReflect f ∈ rlc_pathVertices gamma'.1 := by
  by_cases hsourcePlanar : sharedPrimalEdge f g ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma'
  · by_cases htargetPlanar : s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_connectorCentralFacePlanarEdges gamma gamma'
    · by_cases hfRight : rlc_dualReflect f ∈ rlc_pathVertices gamma.1
      · exact Or.inr (Or.inr (Or.inl hfRight))
      · by_cases hfLeft : rlc_dualReflect f ∈ rlc_pathVertices gamma'.1
        · exact Or.inr (Or.inr (Or.inr hfLeft))
        · exfalso
          have hsource : RlcTwoChannelFullPhysicalSourceCarrierGeometry
              gamma gamma' f g :=
            rlc_twoChannelFullPhysical_sourceCarrier_of_planar
              gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) hfg hsourcePlanar
          have hcentral : RlcCentralFaceReflectedEdgeCarrierGeometry
              gamma gamma' f g :=
            (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
              gamma gamma' hfg.1).2 htargetPlanar
          have htarget : RlcTwoChannelFullPhysicalTargetCarrierGeometry
              gamma gamma' f g :=
            rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginal
              gamma gamma' hfg hfRight hfLeft hcentral
          have hcarrier : RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
              gamma gamma' f g :=
            (rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
              gamma gamma' f g).2 ⟨htarget, hsource⟩
          obtain ⟨physical, hphysicalMap, hsourceCross⟩ :=
            rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut
              gamma gamma' A hAright hAleft hfg hcarrier
          have htargetCross : rlc_twoChannelFullPhysicalEdgeCrossesCut
              B physical.1.1 :=
            (rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff
              B physical.1.1).2 (by
                rw [hphysicalMap]
                exact hcrossB)
          exact hnoPair ⟨physical, hsourceCross, htargetCross⟩
    · exact Or.inr (Or.inl htargetPlanar)
  · exact Or.inl hsourcePlanar


theorem
    rlc_twoChannelFullPhysical_noPair_orientedBChanging_boundary_not_planar
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
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj f g)
    (hfB : rlc_dualReflect f ∈
      rlc_twoChannelFullPhysicalLiftVertexCut B)
    (hgB : rlc_dualReflect g ∉
      rlc_twoChannelFullPhysicalLiftVertexCut B) :
    sharedPrimalEdge f g ∉
        rlc_connectorCentralFacePlanarEdges gamma gamma' ∨
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  by_cases hsourcePlanar : sharedPrimalEdge f g ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma'
  · by_cases htargetPlanar : s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_connectorCentralFacePlanarEdges gamma gamma'
    · have hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) :=
        ⟨rlc_dualReflect f, rlc_dualReflect g, rfl,
          Or.inl ⟨hfB, hgB⟩⟩
      have hobstruction :=
        rlc_twoChannelFullPhysical_noPair_BChanging_boundary_planar_obstruction
          gamma gamma' A B hAright hAleft hnoPair hfg hcrossB
      have hnotOriginal : s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
        intro horiginal
        rcases Finset.mem_union.mp horiginal with hright | hleft
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
          have hgBox : rlc_dualReflect g ∈
              rect (-2 * n) (2 * n) (-n) n :=
            rlc_rightPathVertex_mem_connectorBox gamma hends.2
          exact hgB ⟨hgBox,
            hBright ⟨rlc_dualReflect g, hgBox⟩ hends.2⟩
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
          obtain ⟨hfBox, hfB'⟩ := hfB
          exact hBleft ⟨rlc_dualReflect f, hfBox⟩ hends.1 hfB'
      have hsource : RlcTwoChannelFullPhysicalSourceCarrierGeometry
          gamma gamma' f g :=
        rlc_twoChannelFullPhysical_sourceCarrier_of_planar
          gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A) hfg hsourcePlanar
      have hcentral : RlcCentralFaceReflectedEdgeCarrierGeometry
          gamma gamma' f g :=
        (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
          gamma gamma' hfg.1).2 htargetPlanar
      have htarget : RlcTwoChannelFullPhysicalTargetCarrierGeometry
          gamma gamma' f g :=
        rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginalEdge
          gamma gamma' hfg hnotOriginal hcentral
      have hcarrier : RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' f g :=
        (rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
          gamma gamma' f g).2 ⟨htarget, hsource⟩
      obtain ⟨physical, hphysicalMap, hsourceCross⟩ :=
        rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut
          gamma gamma' A hAright hAleft hfg hcarrier
      have htargetCross : rlc_twoChannelFullPhysicalEdgeCrossesCut
          B physical.1.1 :=
        (rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff
          B physical.1.1).2 (by
            rw [hphysicalMap]
            exact hcrossB)
      have hfalse : False :=
        hnoPair ⟨physical, hsourceCross, htargetCross⟩
      rcases hobstruction with hbadSource | hbadTarget | hfRight | hfLeft
      · exact False.elim (hbadSource hsourcePlanar)
      · exact False.elim (hbadTarget htargetPlanar)
      · exact False.elim hfalse
      · exact False.elim hfalse
    · exact Or.inr htargetPlanar
  · exact Or.inl hsourcePlanar


theorem
    rlc_twoChannelFullPhysical_contactCycle_BChanging_not_planar_of_noPair
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
        rlc_dualReflect f ∈
          rlc_twoChannelFullPhysicalLiftVertexCut B ∧
        rlc_dualReflect g ∉
          rlc_twoChannelFullPhysicalLiftVertexCut B ∧
        (sharedPrimalEdge f g ∉
            rlc_connectorCentralFacePlanarEdges gamma gamma' ∨
          s(rlc_dualReflect f, rlc_dualReflect g) ∉
            rlc_connectorCentralFacePlanarEdges gamma gamma') := by
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hxBox : rlc_dualReflect x ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_rightPathVertex_mem_connectorBox gamma hxPath
  have hyBox : rlc_dualReflect y ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_leftPathVertex_mem_connectorBox gamma' hyPath
  have hxB : rlc_dualReflect x ∈
      rlc_twoChannelFullPhysicalLiftVertexCut B :=
    ⟨hxBox, hBright ⟨rlc_dualReflect x, hxBox⟩ hxPath⟩
  have hyB : rlc_dualReflect y ∉
      rlc_twoChannelFullPhysicalLiftVertexCut B := by
    rintro ⟨_hyBox, hyB⟩
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
  refine ⟨f, g, hfgCycle, hfB, hgB, ?_⟩
  exact
    rlc_twoChannelFullPhysical_noPair_orientedBChanging_boundary_not_planar
      gamma gamma' A B hAright hAleft hBright hBleft hnoPair
        hfgBoundary hfB hgB


theorem rlc_twoChannelFullPhysical_sourceBad_not_planar
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hbadSource : ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
      gamma gamma' f g) :
    sharedPrimalEdge f g ∉
      rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  intro hplanar
  exact hbadSource
    (rlc_twoChannelFullPhysical_sourceCarrier_of_planar
      gamma gamma' omega hfg hplanar)


theorem rlc_twoChannelFullPhysical_reachable_interior_nonbarrier_edge_planar
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {p q : Site 2}
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
      -n < p 1 ∧ p 1 < n)
    (hpBarrier : p ∉ rlc_connectorBarrier gamma gamma')
    (hqBox : q ∈ rlc_connectorBox n)
    (hpqAdj : (hypercubicLattice 2).Adj p q) :
    s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  obtain ⟨hpBox, hpConnected⟩ := hpReach
  obtain ⟨w⟩ := hpConnected
  cases w.reverse with
  | nil =>
      exact False.elim (hpBarrier (by
        simp [rlc_connectorRightAnchor, rlc_connectorBarrier,
          rlc_path_start_mem_vertices gamma.1]))
  | @cons _ z _ hpz tail =>
      have hpzOpen : rlc_twoChannelFullAmbientConfig gamma gamma' omega
          s(p, (z : Site 2)) = true := by
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hpz
        exact hpz.2
      have hpzPlanar :=
        rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
          gamma gamma' omega hpzOpen
      have hpzAdj : (hypercubicLattice 2).Adj p (z : Site 2) := by
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hpz
        exact hpz.1
      rw [rlc_mem_connectorCentralFacePlanarEdges_iff
        gamma gamma' hpzAdj] at hpzPlanar
      rcases hpzPlanar with hpzWall |
          ⟨hpConnectorBox, _hzConnectorBox, h, hhRegion, hhFlank⟩
      · exact False.elim (hpBarrier
          (rlc_mem_connectorBarrier_of_mem_fourTraceEdge
            gamma gamma' hpzWall (Sym2.mem_mk_left _ _)))
      · generalize hkEq : flankFaces p q = e
        induction e using Sym2.inductionOn with
        | _ k l =>
            have hkFlank : k ∈ flankFaces p q := by
              rw [hkEq]
              exact Sym2.mem_mk_left _ _
            have hkRegion := rlc_centralFaceRegion_flank_transfer_interior
              gamma gamma' hpzAdj hpqAdj hpInterior hpBarrier
                hhRegion hhFlank hkFlank
            exact rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
              gamma gamma' hpqAdj hpConnectorBox hqBox
                hkRegion hkFlank


theorem
    rlc_twoChannelFullPhysical_reachable_interior_edge_planar_or_last_wall_or_opposite
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {p q : Site 2}
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
      -n < p 1 ∧ p 1 < n)
    (hqBox : q ∈ rlc_connectorBox n)
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2))
    (hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      s(p, q) = false) :
    s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨
      ∃ z : Site 2,
        (hypercubicLattice 2).Adj p z ∧
          rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s(p, z) = true ∧
          (s(p, z) ∈ rlc_connectorFourTraceEdges gamma gamma' ∨
            (z 0 + q 0 = 2 * p 0 ∧
              z 1 + q 1 = 2 * p 1)) := by
  obtain ⟨_hpBox, hpConnected⟩ := hpReach
  obtain ⟨w⟩ := hpConnected
  cases w.reverse with
  | nil => exact False.elim (hpAnchor rfl)
  | @cons _ z _ hpz tail =>
      have hpzOpen : rlc_twoChannelFullAmbientConfig gamma gamma' omega
          s(p, (z : Site 2)) = true := by
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hpz
        exact hpz.2
      have hpzAdj : (hypercubicLattice 2).Adj p (z : Site 2) := by
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hpz
        exact hpz.1
      have hpzPlanar :=
        rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
          gamma gamma' omega hpzOpen
      by_cases hpzWall : s(p, (z : Site 2)) ∈
          rlc_connectorFourTraceEdges gamma gamma'
      · exact Or.inr ⟨z, hpzAdj, hpzOpen, Or.inl hpzWall⟩
      · rw [rlc_mem_connectorCentralFacePlanarEdges_iff
          gamma gamma' hpzAdj] at hpzPlanar
        rcases hpzPlanar with hpzWall' |
            ⟨_hpBox, _hzBox, h, hhRegion, hhFlank⟩
        · exact False.elim (hpzWall hpzWall')
        · have hzq : (z : Site 2) ≠ q := by
            intro hzq
            have heq : s(p, (z : Site 2)) = s(p, q) := by rw [hzq]
            rw [heq, hpqClosed] at hpzOpen
            contradiction
          by_cases hopp : (z : Site 2) 0 + q 0 = 2 * p 0 ∧
              (z : Site 2) 1 + q 1 = 2 * p 1
          · exact Or.inr ⟨z, hpzAdj, hpzOpen, Or.inr hopp⟩
          · left
            exact rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident
              gamma gamma' hpzAdj hpqAdj hzq hopp hpInterior hpzWall
                hhRegion hhFlank


end
end StatMech.Universality
