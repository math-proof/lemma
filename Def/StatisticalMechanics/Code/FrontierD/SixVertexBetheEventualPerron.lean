/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexEventuallyHasSymmetricBetheIdentification
    {c : Real} (hc : 2 < c) : Prop :=
  ∀ᶠ k : Nat in atTop,
    sixVertexLambdaAlongFour c 0 k =
      sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc k)

end
end StatMech.FrontierD
