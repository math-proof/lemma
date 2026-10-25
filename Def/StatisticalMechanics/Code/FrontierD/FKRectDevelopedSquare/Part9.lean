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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part8
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectDevelopedSquareHorizontalEndpointPairs (n : Nat) :
    Finset ((StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) := by
  classical
  letI := (StatMech.RSW.Box.rect_finite 0 n 0 n).fintype
  exact Finset.univ.filter fun p => p.1.1 0 = 0 ∧ p.2.1 0 = n


noncomputable def fkRectDevelopedSquareVerticalEndpointPairs (n : Nat) :
    Finset ((StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) := by
  classical
  letI := (StatMech.RSW.Box.rect_finite 0 n 0 n).fintype
  exact Finset.univ.filter fun p => p.1.1 1 = 0 ∧ p.2.1 1 = n

end
end StatMech.FrontierD
