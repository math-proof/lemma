/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopGeometricDualWeighted
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls

noncomputable section

theorem kwg_pathDefectCount_cutSet (P : PlanarZ2Subgraph)
    (config : ConfigSpace P.V) {u v : P.V} (path : P.G.Walk u v) :
    kwg_pathDefectCount P path
        (kwg_cutSet (kwg_primalEnds P) config) =
      kwd_crossCount (kwd_sideBoundary config) path := by
  unfold kwg_pathDefectCount kwg_pathEdgeIndices kwd_crossCount
  rw [List.countP_map]
  calc
    _ = path.edges.attach.countP
        (kwd_sideBoundary config ∘ Subtype.val) := by
      apply List.countP_congr
      intro edge _
      simp only [Function.comp_apply, kwg_pathEdgeIndex,
        decide_eq_true_eq]
      rw [kwg_mem_cutSet]
      rcases edge with ⟨edge, hedge⟩
      induction edge using Sym2.ind with
      | _ x y =>
          have hadj := path.adj_of_mem_edges hedge
          rw [kwg_primalEnds, kwg_isSplit_mk, kwd_sideBoundary_mk]
          cases config x <;> cases config y <;> decide
    _ = (path.edges.attach.map Subtype.val).countP
        (kwd_sideBoundary config) := by rw [List.countP_map]
    _ = _ := by simp


theorem kwg_pathDefectSign_cutSet (P : PlanarZ2Subgraph)
    (config : ConfigSpace P.V) {u v : P.V} (path : P.G.Walk u v) :
    kwg_pathDefectSign P path
        (kwg_cutSet (kwg_primalEnds P) config) =
      ons_lowTempPathSign P.G config path := by
  unfold kwg_pathDefectSign ons_lowTempPathSign
  rw [kwg_pathDefectCount_cutSet]


end
end StatMech.Onsager
