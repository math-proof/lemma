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
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part10
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDevelopedSquareEndpointConnectionEvent_isIncreasing
    (R : FKRectTorus) (n : Nat)
    (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) :
    IsIncreasing (fkRectDevelopedSquareEndpointConnectionEvent R n p) := by
  intro omega tau hot hconn
  exact StatMech.TwoDim.connectedWithin_mono
    (fkRectDevelopedSquarePullback_mono R n hot) hconn


theorem fkRectDevelopedSquareEndpointConnection_imp_torusReachable
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration)
    (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n))
    (hconn : omega ∈ fkRectDevelopedSquareEndpointConnectionEvent R n p) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectDevelopedSquareVertex R n p.1)
      (fkRectDevelopedSquareVertex R n p.2) := by
  exact hconn.map (fkRectDevelopedSquareOpenHom
    R n hwidth hheight omega)


end
end StatMech.FrontierD
