/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexLoopDecoratedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) :=
  Sigma fun pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right =>
    SixVertexCompatibleLoopPairing pair.1.1 ×
      SixVertexCompatibleLoopPairing pair.2.1


end
end StatMech.FrontierD
