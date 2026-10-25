/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part5
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectDevelopedSquareFaceDualToDualPullbackHom
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration) :
    (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).induce
          (StatMech.RSW.Box.rect 0 n 0 n) →g
      (openSubgraph 2
        (fkRectDevelopedSquarePullback R n
          (fkRectDualConfigurationEquiv R omega))).induce
            (StatMech.RSW.Box.rect 0 n 0 n) where
  toFun z := ⟨z.1, z.2⟩
  map_rel' := by
    intro z w hzw
    have htorus := fkRectDevelopedSquare_faceDual_adj_imp_dual_adj
      R n hn hwidth hheight omega z.2 w.2 hzw
    change (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).Adj z.1 w.1 at hzw
    change (openSubgraph 2
      (fkRectDevelopedSquarePullback R n
        (fkRectDualConfigurationEquiv R omega))).Adj z.1 w.1
    rw [openSubgraph_adj] at hzw ⊢
    exact ⟨hzw.1, (fkRectDevelopedSquarePullback_open_iff
      R n hwidth hheight (fkRectDualConfigurationEquiv R omega)
      z.2 w.2 hzw.1).mpr htorus⟩


end
end StatMech.FrontierD
