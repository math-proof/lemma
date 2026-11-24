module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey.Part2
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7
public import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

open Finset

namespace SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets

noncomputable def key
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1.1) :=
  sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey T middle
    hmiddle_pos hmiddle_lt grade targets.single source

noncomputable def branchKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1.1) :=
  (targets.key source).paired
    (sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo source.1) branch

end SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
end
end StatMech.FrontierD
