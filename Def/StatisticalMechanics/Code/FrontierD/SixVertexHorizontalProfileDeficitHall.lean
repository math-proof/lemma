/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileDeficitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalProfileDeficit
    {T : EvenTorus}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) : Nat :=
  (-sixVertexHorizontalProfileSignedKernel
    sourceLeft sourceRight targetLeft targetRight profile).toNat

def sixVertexHorizontalProfileSurplus
    {T : EvenTorus}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) : Nat :=
  (sixVertexHorizontalProfileSignedKernel
    sourceLeft sourceRight targetLeft targetRight profile).toNat

end
end StatMech.FrontierD
