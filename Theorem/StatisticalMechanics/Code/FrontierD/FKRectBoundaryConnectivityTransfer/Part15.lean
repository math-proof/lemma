/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part17
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectStripGraph_succ_adj_iff
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin (n + 1) -> Bool × (Bool × Fin W -> Bool))
    (u v : FKRectStripVertex W (n + 1)) :
    (fkRectStripGraph hW (n + 1) layers).Adj u v ↔
      ((fkRectStripGraph hW n (fun i => layers i.castSucc)).sum
        (⊥ : SimpleGraph (Fin W))).Adj u v ∨
      ∃ a : Bool × Fin W, (layers (Fin.last n)).2 a = true ∧
        (SimpleGraph.edge
          (fkRectStripLayerEmbed n
            (fkRectLayerEdgeEndpoints hW (layers (Fin.last n)).1 a).1)
          (fkRectStripLayerEmbed n
            (fkRectLayerEdgeEndpoints hW (layers (Fin.last n)).1 a).2)).Adj u v := by
  rw [fkRectStripGraph, finiteBoundaryEdgeRun_adj_iff]
  unfold fkRectBoundaryOpenLayerEdges fkRectBoundaryOpenLayerIndices
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and]
  aesop


theorem fkRectOpenEdgeCount_eq_sum_layerOpenCount
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenEdgeCount R omega =
      ∑ y : Fin R.height,
        fkRectBoundaryLayerOpenCount (fkRectConfigurationLayer R omega y) := by
  classical
  unfold fkRectOpenEdgeCount fkRectBoundaryLayerOpenCount
  simp only [Finset.card_filter, Fintype.sum_prod_type,
    fkRectConfigurationLayer]
  calc
    (∑ b : Bool, ∑ x : Fin R.width, ∑ y : Fin R.height,
        if omega (b, (x, y)) = true then 1 else 0) =
        ∑ b : Bool, ∑ y : Fin R.height, ∑ x : Fin R.width,
          if omega (b, (x, y)) = true then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.sum_comm]
    _ = ∑ y : Fin R.height, ∑ b : Bool, ∑ x : Fin R.width,
          if omega (b, (x, y)) = true then 1 else 0 := by
            rw [Finset.sum_comm]


end
end StatMech.FrontierD
