module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

instance sixVertexResolvedCrossRoutedKeyPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

end
end StatMech.FrontierD
