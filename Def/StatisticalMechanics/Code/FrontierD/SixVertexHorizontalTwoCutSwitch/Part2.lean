/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalTwoCutSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalPairColumnAgreementCount
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (i : Fin T.width) : Nat :=
  ∑ j : Fin T.height,
    sixVertexHorizontalPairBondAgreementCount horizontal (i, j)

def sixVertexHorizontalPairColumnCrossAgreementCount
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (i : Fin T.width) : Nat :=
  ∑ j : Fin T.height,
    sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j)


def SixVertexHorizontalPairTwoCutBalanced
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (a b : Fin T.width) : Prop :=
  sixVertexHorizontalPairColumnCrossAgreementCount horizontal a +
      sixVertexHorizontalPairColumnCrossAgreementCount horizontal b =
    sixVertexHorizontalPairColumnAgreementCount horizontal a +
      sixVertexHorizontalPairColumnAgreementCount horizontal b

end
end StatMech.FrontierD
