/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


def fkOrientedMedialLoopVerticalFlux
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (C : FKMedialLoop T pairing) : Int := by
  classical
  exact ∑ i : Fin T.width,
    if (fkMedialLoopGraph T pairing).connectedComponentMk
          (fkMedialVerticalSeamDart T i) = C then
      fkOrientedVerticalSeamSign T arrows i
    else 0


def fkMedialCheckerArrows (T : EvenTorus) : SixVertexArrows T where
  horizontal v := !fkMedialCheckerColor (v, .east)
  vertical v := !fkMedialCheckerColor (v, .north)

end
end StatMech.FrontierD
