/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideDual
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def fkRectWideExteriorOpenExtensionToSwapHom
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 (fkRectWideExteriorOpenExtension n eta)
        (rect 0 n 0 (3 * n)) →g
      openSubgraphInduce 2 (StatMech.Universality.crf_swapConfig eta)
        (rect 0 n 0 (3 * n)) where
  toFun z := ⟨z.1, z.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy ⊢
    refine ⟨hxy.1, ?_⟩
    have hx : (x : Site 2) ∈ fkRectWideTallFinset n := by
      simpa [fkRectWideTallFinset] using x.2
    have hy : (y : Site 2) ∈ fkRectWideTallFinset n := by
      simpa [fkRectWideTallFinset] using y.2
    have he : s((x : Site 2), (y : Site 2)) ∈
        StatMech.Percolation.edgesWithinFinset
          (fkRectWideTallFinset n) := by
      rw [StatMech.Percolation.mem_edgesWithinFinset]
      exact ⟨x, hx, y, hy, rfl⟩
    rw [fkRectWideExteriorOpenExtension_eq_swap_of_mem n eta he] at hxy
    change StatMech.Universality.crf_swapConfig eta
      s((x : Site 2), (y : Site 2)) = true
    exact hxy.2


end
end StatMech.FrontierD
