/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

def fkRectIntegralSquareDartEnd (d : FKRectIntegralSquareDart) : Int × Int :=
  (d.1.1 + ons_dirExponentX d.2,
    d.1.2 + ons_dirExponentY d.2)


def fkRectIntegralSquareDartMod (L : Nat) (d : FKRectIntegralSquareDart) :
    ons_Dart L :=
  (((d.1.1 : ZMod L), (d.1.2 : ZMod L)), d.2)

end
end StatMech.FrontierD
