module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey.Part2
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7


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

instance degreeTwoHighChargeSpliceHallDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p


end
end StatMech.FrontierD
