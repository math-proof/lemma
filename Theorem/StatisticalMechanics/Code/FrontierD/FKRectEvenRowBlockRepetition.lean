/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectEvenRowTranslatedConnectionEvent_isIncreasing
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S) (shift : Nat) :
    IsIncreasing
      (fkRectEvenRowTranslatedConnectionEvent R S x y shift) :=
  fkRectConnectedWithin_isIncreasing R
    (fkRectEvenRowTranslationSet R shift S)
    (fkRectEvenRowTranslationSetEquiv R shift S x)
    (fkRectEvenRowTranslationSetEquiv R shift S y)


theorem fkRectCritical_evenRowTranslatedConnectionMass
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S)
    (shift : Nat) (hshift : Even shift) (q : Real) :
    fkRectCriticalEventMass R q
        (fkRectEvenRowTranslatedConnectionEvent R S x y shift) =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  exact fkRectCritical_connectedWithinMass_evenRowTranslation
    R shift hshift q S x y


end
end StatMech.FrontierD
