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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part3
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectDevelopedSquareOpenHom
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration) :
    (openSubgraph 2 (fkRectDevelopedSquarePullback R n omega)).induce
        (StatMech.RSW.Box.rect 0 n 0 n) →g
      fkRectOpenGraph R omega where
  toFun z := fkRectDevelopedSquareVertex R n z
  map_rel' := by
    intro z w hzw
    change (openSubgraph 2
      (fkRectDevelopedSquarePullback R n omega)).Adj z.1 w.1 at hzw
    rw [openSubgraph_adj] at hzw
    exact (fkRectDevelopedSquarePullback_open_iff R n hwidth hheight
      omega z.2 w.2 hzw.1).mp hzw.2


def fkRectDevelopedSquareHorizontalCrossingEvent
    (R : FKRectTorus) (n : Nat) : Set R.Configuration :=
  {omega | StatMech.RSW.Box.HorizontalCrossing
    (fkRectDevelopedSquarePullback R n omega) 0 n 0 n}

end
end StatMech.FrontierD
