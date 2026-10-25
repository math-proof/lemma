/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalTwoCutSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch.Part4


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalTwoCutMask
    {T : EvenTorus} (a b : Fin T.width) (x : Fin T.width) : Bool :=
  decide (a.val ≤ x.val ∧ x.val < b.val)


end
end StatMech.FrontierD
