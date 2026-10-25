/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6
import Def.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk


namespace StatMech.Onsager

open Finset SimpleGraph

@[simp] theorem ons_decPortChainWalk_edges_toFinset
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    (ons_decPortChainWalk L site a b).edges.toFinset =
      ons_decChainPathEdges site a b :=
  Classical.choose_spec (ons_exists_decPortChainWalk L site a b)


theorem ons_exists_decPortChainPath
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    ∃ p : (ons_decGraph L).Walk (site, a) (site, b),
      p.IsPath ∧ p.edges.toFinset = ons_decChainPathEdges site a b := by
  fin_cases a <;> fin_cases b
  · refine ⟨.nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj01 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj01 L site)
      (.cons (ons_decGraph_adj12 L site) .nil), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj01 L site)
      (.cons (ons_decGraph_adj12 L site)
        (.cons (ons_decGraph_adj23 L site) .nil)), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj10 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj12 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj12 L site)
      (.cons (ons_decGraph_adj23 L site) .nil), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj21 L site)
      (.cons (ons_decGraph_adj10 L site) .nil), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (1 : Fin 4)), (site, (0 : Fin 4))) =
      s((site, (0 : Fin 4)), (site, (1 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj21 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj23 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj32 L site)
      (.cons (ons_decGraph_adj21 L site)
        (.cons (ons_decGraph_adj10 L site) .nil)), by simp, ?_⟩
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
      (.cons (ons_decGraph_adj21 L site) .nil), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show s((site, (3 : Fin 4)), (site, (2 : Fin 4))) =
      s((site, (2 : Fin 4)), (site, (3 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj32 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]

end StatMech.Onsager
