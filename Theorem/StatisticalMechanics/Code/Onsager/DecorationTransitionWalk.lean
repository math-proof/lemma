/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_decGraph_adj_of_portLineAdj
    (L : ℕ) (site : ZMod L × ZMod L) {a b : Fin 4}
    (h : ons_portLineAdj a b) :
    (ons_decGraph L).Adj (site, a) (site, b) :=
  Or.inr ⟨rfl, h⟩

theorem ons_decGraph_adj01 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 0) (site, 1) :=
  ons_decGraph_adj_of_portLineAdj L site (by left; norm_num)

theorem ons_decGraph_adj10 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 1) (site, 0) :=
  ons_decGraph_adj_of_portLineAdj L site (by right; norm_num)

theorem ons_decGraph_adj12 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 1) (site, 2) :=
  ons_decGraph_adj_of_portLineAdj L site (by left; norm_num)

theorem ons_decGraph_adj21 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 2) (site, 1) :=
  ons_decGraph_adj_of_portLineAdj L site (by right; norm_num)

theorem ons_decGraph_adj23 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 2) (site, 3) :=
  ons_decGraph_adj_of_portLineAdj L site (by left; norm_num)

theorem ons_decGraph_adj32 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 3) (site, 2) :=
  ons_decGraph_adj_of_portLineAdj L site (by right; norm_num)

@[simp] theorem ons_decChainPathIndices_00 :
    ons_decChainPathIndices 0 0 = ∅ := by decide

@[simp] theorem ons_decChainPathIndices_01 :
    ons_decChainPathIndices 0 1 = {0} := by decide

@[simp] theorem ons_decChainPathIndices_02 :
    ons_decChainPathIndices 0 2 = {0, 1} := by decide

@[simp] theorem ons_decChainPathIndices_03 :
    ons_decChainPathIndices 0 3 = Finset.univ := by decide

@[simp] theorem ons_decChainPathIndices_10 :
    ons_decChainPathIndices 1 0 = {0} := by decide

@[simp] theorem ons_decChainPathIndices_11 :
    ons_decChainPathIndices 1 1 = ∅ := by decide

@[simp] theorem ons_decChainPathIndices_12 :
    ons_decChainPathIndices 1 2 = {1} := by decide

@[simp] theorem ons_decChainPathIndices_13 :
    ons_decChainPathIndices 1 3 = {1, 2} := by decide

@[simp] theorem ons_decChainPathIndices_20 :
    ons_decChainPathIndices 2 0 = {0, 1} := by decide

@[simp] theorem ons_decChainPathIndices_21 :
    ons_decChainPathIndices 2 1 = {1} := by decide

@[simp] theorem ons_decChainPathIndices_22 :
    ons_decChainPathIndices 2 2 = ∅ := by decide

@[simp] theorem ons_decChainPathIndices_23 :
    ons_decChainPathIndices 2 3 = {2} := by decide

@[simp] theorem ons_decChainPathIndices_30 :
    ons_decChainPathIndices 3 0 = Finset.univ := by decide

@[simp] theorem ons_decChainPathIndices_31 :
    ons_decChainPathIndices 3 1 = {1, 2} := by decide

@[simp] theorem ons_decChainPathIndices_32 :
    ons_decChainPathIndices 3 2 = {2} := by decide

@[simp] theorem ons_decChainPathIndices_33 :
    ons_decChainPathIndices 3 3 = ∅ := by decide


theorem ons_exists_decPortChainWalk
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    ∃ p : (ons_decGraph L).Walk (site, a) (site, b),
      p.edges.toFinset = ons_decChainPathEdges site a b := by
  fin_cases a <;> fin_cases b
  · refine ⟨.nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj01 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj01 L site)
      (.cons (ons_decGraph_adj12 L site) .nil), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj01 L site)
      (.cons (ons_decGraph_adj12 L site)
        (.cons (ons_decGraph_adj23 L site) .nil)), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj10 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj12 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj12 L site)
      (.cons (ons_decGraph_adj23 L site) .nil), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj21 L site)
      (.cons (ons_decGraph_adj10 L site) .nil), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (1 : Fin 4)), (site, (0 : Fin 4))) =
      s((site, (0 : Fin 4)), (site, (1 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj21 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj23 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj32 L site)
      (.cons (ons_decGraph_adj21 L site)
        (.cons (ons_decGraph_adj10 L site) .nil)), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [show s((site, (3 : Fin 4)), (site, (2 : Fin 4))) =
      s((site, (2 : Fin 4)), (site, (3 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (1 : Fin 4)), (site, (0 : Fin 4))) =
      s((site, (0 : Fin 4)), (site, (1 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj32 L site)
      (.cons (ons_decGraph_adj21 L site) .nil), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show s((site, (3 : Fin 4)), (site, (2 : Fin 4))) =
      s((site, (2 : Fin 4)), (site, (3 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj32 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]


end StatMech.Onsager
