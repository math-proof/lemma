/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

def SixVertexLoopDecoratedPairTotalCReconnection
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  exists matching : SixVertexLoopDecoratedPair T lower upper ->
      SixVertexLoopDecoratedPair T middle middle,
    Function.Injective matching /\
      forall source,
        sixVertexLoopDecoratedPairTotalC source =
          sixVertexLoopDecoratedPairTotalC (matching source)


end
end StatMech.FrontierD
