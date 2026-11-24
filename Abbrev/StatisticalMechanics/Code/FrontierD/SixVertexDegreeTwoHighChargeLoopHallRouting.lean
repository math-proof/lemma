module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part2
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalDegreeTwoLoopHallSource
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  {source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) //
    sixVertexLoopDecoratedPairBigrade source = grade}

abbrev SixVertexHorizontalDegreeTwoLoopHallTarget
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (grade : Nat × Nat) :=
  {target : SixVertexLoopDecoratedPair T middle middle //
    sixVertexLoopDecoratedPairBigrade target = grade}


end
end StatMech.FrontierD
