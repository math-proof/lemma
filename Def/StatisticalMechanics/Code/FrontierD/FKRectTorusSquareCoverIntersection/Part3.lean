module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
public import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part3
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

def fkRectNatScale (n : Nat) (u : Int × Int) : Int × Int :=
  ((n : Int) * u.1, (n : Int) * u.2)


def fkRectRepeatTranslatedDartPath
    (l : List FKRectIntegralSquareDart) (u : Int × Int) :
    Nat → List FKRectIntegralSquareDart
  | 0 => []
  | n + 1 =>
      fkRectRepeatTranslatedDartPath l u n ++
        l.map (fkRectIntegralSquareDartTranslate (fkRectNatScale n u))

end
end StatMech.FrontierD
