module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

instance positiveUnitComponentResidualRoutingDecidableProp (p : Prop) :
    Decidable p := Classical.propDecidable p


end
end StatMech.FrontierD
