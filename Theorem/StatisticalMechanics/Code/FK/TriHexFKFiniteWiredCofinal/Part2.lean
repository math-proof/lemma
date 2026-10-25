/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

@[simp] theorem triHexPlanarFiniteStarVertexEmbedding_cell
    (n : Nat) (z : TriHexPlanarFiniteCell n) :
    triHexPlanarFiniteStarVertexEmbedding n (Sum.inl z) = (z.1, false) := rfl

@[simp] theorem triHexPlanarFiniteStarVertexEmbedding_terminal
    (n : Nat) (v : TriHexPlanarFiniteTerminal n) :
    triHexPlanarFiniteStarVertexEmbedding n (Sum.inr v) = (v.1, true) := rfl


theorem triHexPlanarFiniteStarGraph_adj_hexagonal
    (n : Nat) {u v : TriHexPlanarFiniteStarVertex n}
    (huv : (triHexPlanarFiniteStarGraph n).Adj u v) :
    hexagonalGraph.Adj
      (triHexPlanarFiniteStarVertexEmbedding n u)
      (triHexPlanarFiniteStarVertexEmbedding n v) := by
  rw [triHexPlanarFiniteStarGraph, SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨⟨z, i⟩, hedge⟩, _⟩ := huv
  change s(Sum.inl z,
    Sum.inr (triHexPlanarFiniteTerminalMap n z i)) = s(u, v) at hedge
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · subst u
    subst v
    simpa [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal] using
      hexagonalGraph_adj_triHexPlanarCellTerminal z.1 i
  · subst u
    subst v
    exact (by
      simpa [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal] using
        (hexagonalGraph_adj_triHexPlanarCellTerminal z.1 i).symm)


theorem triHexPlanarFiniteStarGraph_adj_of_hexagonal
    (n : Nat) {u v : TriHexPlanarFiniteStarVertex n}
    (huv : hexagonalGraph.Adj
      (triHexPlanarFiniteStarVertexEmbedding n u)
      (triHexPlanarFiniteStarVertexEmbedding n v)) :
    (triHexPlanarFiniteStarGraph n).Adj u v := by
  rcases u with z | x <;> rcases v with w | y
  · simp [hexagonalGraph_adj, hexagonalAdj] at huv
  · rw [hexagonalGraph_adj] at huv
    rcases huv with ⟨_, _, i, hi⟩ | hbad
    · change y.1 - z.1 = hexagonalStep i at hi
      have hxy : y.1 = triHexPlanarCellTerminal z.1 i := by
        rw [triHexPlanarCellTerminal]
        exact eq_add_of_sub_eq' hi
      have hterm : y = triHexPlanarFiniteTerminalMap n z i :=
        Subtype.ext hxy
      subst y
      rw [triHexPlanarFiniteStarGraph, SimpleGraph.fromEdgeSet_adj]
      refine ⟨⟨(z, i), rfl⟩, Sum.inl_ne_inr⟩
    · simp at hbad
  · rw [hexagonalGraph_adj] at huv
    rcases huv with hbad | ⟨_, _, i, hi⟩
    · simp at hbad
    · change x.1 - w.1 = hexagonalStep i at hi
      have hxy : x.1 = triHexPlanarCellTerminal w.1 i := by
        rw [triHexPlanarCellTerminal]
        exact eq_add_of_sub_eq' hi
      have hterm : x = triHexPlanarFiniteTerminalMap n w i :=
        Subtype.ext hxy
      subst x
      rw [triHexPlanarFiniteStarGraph, SimpleGraph.fromEdgeSet_adj]
      refine ⟨⟨(w, i), ?_⟩, Sum.inr_ne_inl⟩
      change s(Sum.inl w,
        Sum.inr (triHexPlanarFiniteTerminalMap n w i)) =
          s(Sum.inr (triHexPlanarFiniteTerminalMap n w i), Sum.inl w)
      rw [Sym2.eq_iff]
      exact Or.inr ⟨rfl, rfl⟩
  · simp [hexagonalGraph_adj, hexagonalAdj] at huv


theorem triHexPlanarFiniteStarGraph_adj_iff_hexagonal
    (n : Nat) (u v : TriHexPlanarFiniteStarVertex n) :
    (triHexPlanarFiniteStarGraph n).Adj u v ↔
      hexagonalGraph.Adj
        (triHexPlanarFiniteStarVertexEmbedding n u)
        (triHexPlanarFiniteStarVertexEmbedding n v) :=
  ⟨triHexPlanarFiniteStarGraph_adj_hexagonal n,
    triHexPlanarFiniteStarGraph_adj_of_hexagonal n⟩


theorem triHexPlanarFiniteStar_adjMatch_hexagonal (n : Nat) :
    ocd_AdjMatch (triHexPlanarFiniteStarGraph n) hexagonalGraph
      (triHexPlanarFiniteStarVertexEmbedding n) :=
  triHexPlanarFiniteStarGraph_adj_iff_hexagonal n


theorem triHexPlanarFiniteStar_cell_not_boundary
    (n : Nat) (z : TriHexPlanarFiniteCell n) :
    ¬ ∃ w : HexVertex,
      hexagonalGraph.Adj
          (triHexPlanarFiniteStarVertexEmbedding n (Sum.inl z)) w ∧
        w ∉ Set.range (triHexPlanarFiniteStarVertexEmbedding n) := by
  rintro ⟨w, hadj, hw⟩
  rw [hexagonalGraph_adj] at hadj
  rcases hadj with ⟨_, hwWhite, i, hi⟩ | hbad
  · have hsite : w.1 = triHexPlanarCellTerminal z.1 i := by
      rw [triHexPlanarCellTerminal]
      change w.1 - z.1 = hexagonalStep i at hi
      exact eq_add_of_sub_eq' hi
    have hwEq : w =
        triHexPlanarFiniteStarVertexEmbedding n
          (Sum.inr (triHexPlanarFiniteTerminalMap n z i)) := by
      apply Prod.ext
      · simpa [triHexPlanarFiniteTerminalMap] using hsite
      · simpa using hwWhite.symm
    exact hw ⟨Sum.inr (triHexPlanarFiniteTerminalMap n z i), hwEq.symm⟩
  · simp at hbad


theorem triHexPlanarFiniteStar_terminal_boundary_iff
    (n : Nat) (v : TriHexPlanarFiniteTerminal n) :
    triHexPlanarFiniteStarBoundary n (Sum.inr v) ↔
      ∃ w : HexVertex,
        hexagonalGraph.Adj
            (triHexPlanarFiniteStarVertexEmbedding n (Sum.inr v)) w ∧
          w ∉ Set.range (triHexPlanarFiniteStarVertexEmbedding n) := by
  constructor
  · rintro ⟨i, hi⟩
    let w : HexVertex := (v.1 - hexagonalStep i, false)
    refine ⟨w, ?_, ?_⟩
    · rw [hexagonalGraph_adj]
      right
      refine ⟨rfl, rfl, i, ?_⟩
      change v.1 - (v.1 - hexagonalStep i) = hexagonalStep i
      abel
    · rintro ⟨u, hu⟩
      rcases u with z | x
      · have hsite := congrArg (fun a : HexVertex => a.1) hu
        apply hi
        change z.1 = v.1 - hexagonalStep i at hsite
        rw [← hsite]
        exact z.2
      · have hlabel := congrArg (fun a : HexVertex => a.2) hu
        simp [w] at hlabel
  · rintro ⟨w, hadj, hw⟩
    rw [hexagonalGraph_adj] at hadj
    rcases hadj with hbad | ⟨hwBlack, _, i, hi⟩
    · simp at hbad
    · refine ⟨i, ?_⟩
      change v.1 - hexagonalStep i ∉ box 2 n
      intro hcenter
      let z : TriHexPlanarFiniteCell n :=
        ⟨v.1 - hexagonalStep i, hcenter⟩
      apply hw
      refine ⟨Sum.inl z, ?_⟩
      apply Prod.ext
      · change z.1 = w.1
        change v.1 - w.1 = hexagonalStep i at hi
        dsimp only [z]
        rw [← hi]
        abel
      · simpa using hwBlack.symm


theorem triHexPlanarFiniteStar_boundary_iff_ambient
    (n : Nat) (u : TriHexPlanarFiniteStarVertex n) :
    triHexPlanarFiniteStarBoundary n u ↔
      ∃ w : HexVertex,
        hexagonalGraph.Adj
            (triHexPlanarFiniteStarVertexEmbedding n u) w ∧
          w ∉ Set.range (triHexPlanarFiniteStarVertexEmbedding n) := by
  rcases u with z | v
  · simp only [triHexPlanarFiniteStarBoundary]
    exact (iff_false_intro
      (triHexPlanarFiniteStar_cell_not_boundary n z)).symm
  · exact triHexPlanarFiniteStar_terminal_boundary_iff n v


theorem triHexPlanarFiniteStar_range_subset_orbitBox_succ (n : Nat) :
    Set.range (triHexPlanarFiniteStarVertexEmbedding n) ⊆
      (hexagonal.orbitBox (n + 1) : Set HexVertex) := by
  rintro v ⟨u, rfl⟩
  change triHexPlanarFiniteStarVertexEmbedding n u ∈
    hexagonal.orbitBox (n + 1)
  rw [hexagonal_mem_orbitBox_iff_box]
  rcases u with z | x
  · exact box_mono 2 (Nat.le_succ n) z.2
  · obtain ⟨zi, hzi, hx⟩ := Finset.mem_image.mp x.2
    obtain ⟨z, i⟩ := zi
    rw [Finset.mem_product] at hzi
    change triHexPlanarCellTerminal z i = x.1 at hx
    change x.1 ∈ box 2 (n + 1)
    rw [← hx]
    exact triHexPlanarCellTerminal_mem_box_succ n (by simpa using hzi.1) i


theorem hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
    (n : Nat) :
    (hexagonal.orbitBox n : Set HexVertex) ⊆
      Set.range (triHexPlanarFiniteStarVertexEmbedding (n + 1)) := by
  intro v hv
  change v ∈ hexagonal.orbitBox n at hv
  rw [hexagonal_mem_orbitBox_iff_box] at hv
  rcases v with ⟨v, b⟩
  cases b
  · let z : TriHexPlanarFiniteCell (n + 1) :=
      ⟨v, box_mono 2 (Nat.le_succ n) hv⟩
    exact ⟨Sum.inl z, rfl⟩
  · let z : TriHexPlanarFiniteCell (n + 1) :=
      ⟨v - hexagonalStep 0,
        triHexPlanarCellPredecessor_mem_box_succ n hv⟩
    refine ⟨Sum.inr (triHexPlanarFiniteTerminalMap (n + 1) z 0), ?_⟩
    apply Prod.ext
    · change triHexPlanarCellTerminal z.1 0 = v
      dsimp only [z]
      rw [triHexPlanarCellTerminal]
      abel
    · rfl


theorem triHexPlanarFiniteTerminal_subset_triangular_orbitBox_succ
    (n : Nat) (v : TriHexPlanarFiniteTerminal n) :
    v.1 ∈ triangular.orbitBox (n + 1) := by
  rw [triangular_mem_orbitBox_iff_box]
  obtain ⟨zi, hzi, hv⟩ := Finset.mem_image.mp v.2
  obtain ⟨z, i⟩ := zi
  rw [Finset.mem_product] at hzi
  change triHexPlanarCellTerminal z i = v.1 at hv
  rw [← hv]
  exact triHexPlanarCellTerminal_mem_box_succ n (by simpa using hzi.1) i


theorem triangular_orbitBox_subset_triHexPlanarFiniteTerminal_succ
    (n : Nat) {v : Site 2} (hv : v ∈ triangular.orbitBox n) :
    v ∈ triHexPlanarFiniteTerminalFinset (n + 1) := by
  rw [triangular_mem_orbitBox_iff_box] at hv
  let z : TriHexPlanarFiniteCell (n + 1) :=
    ⟨v - hexagonalStep 0,
      triHexPlanarCellPredecessor_mem_box_succ n hv⟩
  apply Finset.mem_image.mpr
  refine ⟨(z.1, 0), ?_, ?_⟩
  · rw [Finset.mem_product]
    exact ⟨by simpa using z.2, Finset.mem_univ 0⟩
  · change triHexPlanarCellTerminal z.1 0 = v
    dsimp only [z]
    rw [triHexPlanarCellTerminal]
    abel


theorem triangularIndexedEdge_rebase_eq_cellEdge
    (z : Site 2) (i : Fin 3) :
    triangularIndexedEdge (triHexPlanarTriangleIndexEquiv (z, i)) =
      s(triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal1 i),
        triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal2 i)) := by
  have hzUnion : z ∈ ⋃ n, box 2 n := by
    rw [iUnion_box]
    trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hzUnion
  let z' : TriHexPlanarFiniteCell n := ⟨z, hn⟩
  have h := triHexPlanarFiniteTriangleEdge_val n (z', i)
  simpa [triHexPlanarFiniteTriangleEdge, triHexPlanarFiniteTerminalMap,
    z'] using h.symm


theorem triHexPlanarFiniteTriangle_adj_or_boundary
    (n : Nat) {u v : TriHexPlanarFiniteTerminal n}
    (huv : triangularGraph.Adj u.1 v.1) :
    (triHexPlanarFiniteTriangleGraph n).Adj u v ∨
      (triHexPlanarFiniteBoundary n u ∧
        triHexPlanarFiniteBoundary n v) := by
  let e : triangularGraph.edgeSet := ⟨s(u.1, v.1), by
    rwa [SimpleGraph.mem_edgeSet]⟩
  let a := triangularEdgeChartEquiv.symm e
  rcases hpair : triHexPlanarTriangleIndexEquiv.symm a with ⟨z, i⟩
  have ha : triHexPlanarTriangleIndexEquiv (z, i) = a := by
    rw [← hpair]
    exact triHexPlanarTriangleIndexEquiv.apply_symm_apply a
  have hchart : triangularIndexedEdge a = s(u.1, v.1) := by
    have h := congrArg Subtype.val
      (triangularEdgeChartEquiv.apply_symm_apply e)
    exact h
  have hedge :
      s(triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal1 i),
        triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal2 i)) =
          s(u.1, v.1) := by
    rw [← hchart, ← ha]
    exact (triangularIndexedEdge_rebase_eq_cellEdge z i).symm
  by_cases hz : z ∈ box 2 n
  · left
    let z' : TriHexPlanarFiniteCell n := ⟨z, hz⟩
    rw [triHexPlanarFiniteTriangleGraph, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨(z', i), ?_⟩, ?_⟩
    · change s(triHexPlanarFiniteTerminalMap n z'
          (triHexTriangleEdgeTerminal1 i),
        triHexPlanarFiniteTerminalMap n z'
          (triHexTriangleEdgeTerminal2 i)) = s(u, v)
      rw [Sym2.eq_iff] at hedge ⊢
      rcases hedge with h | h
      · exact Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩
      · exact Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩
    · exact fun huvEq => huv.ne (congrArg Subtype.val huvEq)
  · right
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · constructor
      · refine ⟨triHexTriangleEdgeTerminal1 i, ?_⟩
        change u.1 - hexagonalStep (triHexTriangleEdgeTerminal1 i) ∉ box 2 n
        rw [← hu]
        simp [triHexPlanarCellTerminal, hz]
      · refine ⟨triHexTriangleEdgeTerminal2 i, ?_⟩
        change v.1 - hexagonalStep (triHexTriangleEdgeTerminal2 i) ∉ box 2 n
        rw [← hv]
        simp [triHexPlanarCellTerminal, hz]
    · constructor
      · refine ⟨triHexTriangleEdgeTerminal2 i, ?_⟩
        change u.1 - hexagonalStep (triHexTriangleEdgeTerminal2 i) ∉ box 2 n
        rw [← hu]
        simp [triHexPlanarCellTerminal, hz]
      · refine ⟨triHexTriangleEdgeTerminal1 i, ?_⟩
        change v.1 - hexagonalStep (triHexTriangleEdgeTerminal1 i) ∉ box 2 n
        rw [← hv]
        simp [triHexPlanarCellTerminal, hz]


theorem triHexPlanarFiniteTriangle_induced_le_wiredGraph (n : Nat) :
    SimpleGraph.comap Subtype.val triangularGraph ≤
      triHexPlanarFiniteTriangleGraph n ⊔
        boundaryCliqueGraph (triHexPlanarFiniteBoundary n) := by
  intro u v huv
  rcases triHexPlanarFiniteTriangle_adj_or_boundary n huv with h | ⟨hu, hv⟩
  · exact Or.inl h
  · right
    rw [boundaryCliqueGraph_adj]
    exact ⟨huv.ne, hu, hv⟩


end
end StatMech.FK.PeriodicPlanar
