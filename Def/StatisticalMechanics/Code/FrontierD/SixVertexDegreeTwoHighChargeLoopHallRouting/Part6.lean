module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
public import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting
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

namespace SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets

noncomputable def routedKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1.1) :=
  sixVertexHorizontalDegreeTwoLoopSynchronizedRoutedKey T middle
    hmiddle_pos hmiddle_lt grade targets.paired source branch


end SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
end
end StatMech.FrontierD
