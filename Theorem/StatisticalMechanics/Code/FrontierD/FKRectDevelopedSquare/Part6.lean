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
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part6
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDevelopedSquare_faceDualVertical_imp_dualVertical
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration)
    (hcross : StatMech.RSW.Box.VerticalCrossing
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega)) 0 n 0 n) :
    StatMech.RSW.Box.VerticalCrossing
      (fkRectDevelopedSquarePullback R n
        (fkRectDualConfigurationEquiv R omega)) 0 n 0 n := by
  obtain ⟨xb, yt, hconn⟩ := hcross
  refine ⟨xb, yt, ?_⟩
  exact hconn.map
    (fkRectDevelopedSquareFaceDualToDualPullbackHom
      R n hn hwidth hheight omega)


end
end StatMech.FrontierD
