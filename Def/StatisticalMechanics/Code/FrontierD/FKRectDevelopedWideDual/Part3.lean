/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideDual.Part2
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def fkRectWideFaceDualSwapHom
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))).induce
          (rect 0 n (-1) (3 * n)) →g
      (openSubgraph 2
        (StatMech.Universality.fci_faceDualConfig eta)).induce
          (rect (-1) (3 * n) 0 n) where
  toFun z := ⟨StatMech.Universality.crf_swap z.1,
    (StatMech.Universality.crf_mem_rect_swap
      0 n (-1) (3 * n) z.1).mp z.2⟩
  map_rel' := by
    intro x y hxy
    exact fkRectWide_faceDualExtension_adj_swap n eta hxy

end
end StatMech.FrontierD
