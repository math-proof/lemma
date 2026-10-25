/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectEvenRowBlockIntersection
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S)
    (step blocks : Nat) : Set R.Configuration :=
  fkRectFiniteEventIntersection (Finset.range blocks) fun i =>
    fkRectEvenRowTranslatedConnectionEvent R S x y (i * step)

end
end StatMech.FrontierD
