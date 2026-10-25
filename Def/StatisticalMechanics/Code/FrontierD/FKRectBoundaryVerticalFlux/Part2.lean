/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryVerticalFlux.Part2
open Equiv Finset SimpleGraph
open StatMech.Onsager StatMech.Onsager.BaseCase


namespace StatMech.FrontierD

noncomputable section

def fkMedialBlackVerticalWrapContribution
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) : Int :=
  let m := fkMedialLocalMate pairing d.1
  if m.2 = .north ∧ m.1.2 = svFinLast T.height_pos then -1
  else if m.2 = .south ∧
      m.1.2 = (⟨0, T.height_pos⟩ : Fin T.height) then 1
  else 0

end
end StatMech.FrontierD
