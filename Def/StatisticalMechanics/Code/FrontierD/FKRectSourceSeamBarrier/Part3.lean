module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBarrierConnectionProduct
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectSourceLeftBarrier (R : FKRectTorus)
    (leftRight : Nat) (gap : R.EdgeIndex) : Set R.Configuration :=
  fkRectNoLeftStripCrossingEvent R leftRight ∩
    fkRectAllButOneOpenSeamEvent R gap

end
end StatMech.FrontierD
