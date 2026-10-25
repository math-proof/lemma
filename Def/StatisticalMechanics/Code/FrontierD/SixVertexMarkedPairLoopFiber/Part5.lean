/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part3
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

def SixVertexCompatibleLoopPairing.toOrientedMedialLoops
    {T : EvenTorus} {omega : SixVertexArrows T}
    (pairing : SixVertexCompatibleLoopPairing omega) :
    FKOrientedMedialLoops T where
  pairing := pairing.1
  arrows := omega
  compatible := pairing.2

end
end StatMech.FrontierD
