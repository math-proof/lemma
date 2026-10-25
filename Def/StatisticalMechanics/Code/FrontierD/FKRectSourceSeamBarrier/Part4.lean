/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBarrierConnectionProduct
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part3


namespace StatMech.FrontierD

noncomputable section

def fkRectSourceBarrierConnectionEvent
    (R : FKRectTorus) (leftRight cut lower upper : Nat)
    (gap : R.EdgeIndex)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper)) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  fkRectRightBandBarrierConnectionEvent R leftRight cut lower upper
    (fkRectHorizontalCutEdges R)
    (fkRectAllButOneOpenConfiguration R gap) t


end
end StatMech.FrontierD
