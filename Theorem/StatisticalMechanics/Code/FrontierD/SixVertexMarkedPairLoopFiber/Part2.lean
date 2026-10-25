/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part3
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexMarkedDecoratedPairZeroEquivLoop_totalC
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (decorated : SixVertexMarkedDecoratedPair T left right 0) :
    sixVertexLoopDecoratedPairTotalC
        (sixVertexMarkedDecoratedPairZeroEquivLoop T left right decorated) =
      sixVertexMarkedDecoratedPairTotalC decorated :=
  rfl


end
end StatMech.FrontierD
