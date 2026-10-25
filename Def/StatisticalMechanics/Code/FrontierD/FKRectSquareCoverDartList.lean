/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSquareCoverDartList.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersectionCriterion


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

def fkRectSquareCoverDartList (R : FKRectTorus)
    (l : List FKRectIntegralSquareDart) (u : Int × Int) :
    List (ons_Dart (fkRectSquareCoverSide R)) :=
  (fkRectRepeatTranslatedDartPath l u (fkRectSquareCoverSide R)).map
    (fkRectIntegralSquareDartMod (fkRectSquareCoverSide R))


end
end StatMech.FrontierD
