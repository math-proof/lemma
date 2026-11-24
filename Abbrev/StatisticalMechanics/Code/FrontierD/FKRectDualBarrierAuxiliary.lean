module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
public import Def.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

abbrev FKRectColumnBandVertex (R : FKRectTorus)
    (left right lower upper : Nat) :=
  FKRectInducedVertex R (fkRectColumnBand R left right lower upper)


end
end StatMech.FrontierD
