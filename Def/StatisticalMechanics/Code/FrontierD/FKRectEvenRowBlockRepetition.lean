/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part7
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectEvenRowTranslatedConnectionEvent
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S) (shift : Nat) :
    Set R.Configuration :=
  {omega | FKRectConnectedWithin R omega
    (fkRectEvenRowTranslationSet R shift S)
    (fkRectEvenRowTranslationSetEquiv R shift S x)
    (fkRectEvenRowTranslationSetEquiv R shift S y)}

end
end StatMech.FrontierD
