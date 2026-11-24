module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredVertexCrossFineRowProfile
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

instance sixVertexColoredFullComponentSwapPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p


end
end StatMech.FrontierD
