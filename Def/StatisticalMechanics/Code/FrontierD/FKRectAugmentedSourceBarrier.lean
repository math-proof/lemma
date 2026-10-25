/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedSourceBarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightBandVerticalWitness.Part3


namespace StatMech.FrontierD

noncomputable section

def fkRectAugmentedSourcePatternEdges (R : FKRectTorus)
    (x : Fin R.width) : Finset R.EdgeIndex :=
  fkRectHorizontalCutEdges R ∪ {fkRectRowZeroAttachmentEdgeAt R x}


def fkRectAugmentedSourceBarrier (R : FKRectTorus)
    (leftRight : Nat) (gap : R.EdgeIndex) (x : Fin R.width) :
    Set R.Configuration :=
  fkRectLeftBarrierWithSeamPattern R leftRight
    (fkRectAugmentedSourcePatternEdges R x)
    (fkRectAllButOneOpenConfiguration R gap)

end
end StatMech.FrontierD
