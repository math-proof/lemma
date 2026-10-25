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
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part9
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem mem_fkRectDevelopedSquareHorizontalEndpointPairs
    (n : Nat) (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) :
    p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n ↔
      p.1.1 0 = 0 ∧ p.2.1 0 = n := by
  classical
  unfold fkRectDevelopedSquareHorizontalEndpointPairs
  simp

theorem mem_fkRectDevelopedSquareVerticalEndpointPairs
    (n : Nat) (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) :
    p ∈ fkRectDevelopedSquareVerticalEndpointPairs n ↔
      p.1.1 1 = 0 ∧ p.2.1 1 = n := by
  classical
  unfold fkRectDevelopedSquareVerticalEndpointPairs
  simp


end
end StatMech.FrontierD
