/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideDual.Part3
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def fkRectDevelopedThreeByOneFaceDualToDualPullbackHom
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration) :
    (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).induce
          (fkRectDevelopedThreeByOneRect n) →g
      (openSubgraph 2
        (fkRectDevelopedSquarePullback R n
          (fkRectDualConfigurationEquiv R omega))).induce
            (fkRectDevelopedThreeByOneRect n) where
  toFun z := ⟨z.1, z.2⟩
  map_rel' := by
    intro z w hzw
    have htorus := fkRectDevelopedThreeByOne_faceDual_adj_imp_dual_adj
      R n hn hwidth hheight omega z.2 w.2 hzw
    change (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).Adj z.1 w.1 at hzw
    change (openSubgraph 2
      (fkRectDevelopedSquarePullback R n
        (fkRectDualConfigurationEquiv R omega))).Adj z.1 w.1
    rw [openSubgraph_adj] at hzw ⊢
    exact ⟨hzw.1, (fkRectDevelopedThreeByOnePullback_open_iff
      R n hwidth hheight (fkRectDualConfigurationEquiv R omega)
      z.2 w.2 hzw.1).mpr htorus⟩


end
end StatMech.FrontierD
