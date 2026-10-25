/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

inductive FKRectIntegralSquareDartPath :
    (Int × Int) → (Int × Int) →
      List FKRectIntegralSquareDart → Prop
  | nil (p : Int × Int) : FKRectIntegralSquareDartPath p p []
  | cons (d : FKRectIntegralSquareDart) {q r l}
      (hend : fkRectIntegralSquareDartEnd d = q)
      (tail : FKRectIntegralSquareDartPath q r l) :
      FKRectIntegralSquareDartPath d.1 r (d :: l)


end
end StatMech.FrontierD
