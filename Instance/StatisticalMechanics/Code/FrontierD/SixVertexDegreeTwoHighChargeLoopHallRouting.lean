module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
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

instance degreeTwoHighChargeLoopHallDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p


end
end StatMech.FrontierD
