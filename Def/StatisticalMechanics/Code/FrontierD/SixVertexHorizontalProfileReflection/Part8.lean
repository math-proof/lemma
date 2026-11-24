module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part7
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexReflectHorizontalPairCompletionProfile
    {T : EvenTorus} (profile : SixVertexHorizontalPairCompletionProfile T) :
    SixVertexHorizontalPairCompletionProfile T :=
  (sixVertexReflectOptionalHorizontalCompletionProfile profile.1,
    sixVertexReflectOptionalHorizontalCompletionProfile profile.2)

end
end StatMech.FrontierD
