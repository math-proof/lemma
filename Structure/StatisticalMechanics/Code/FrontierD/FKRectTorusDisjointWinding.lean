/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part3
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

structure FKRectSquareCoverDartWitness (R : FKRectTorus)
    (u : Int × Int) where
  darts : List (ons_Dart (fkRectSquareCoverSide R))
  balanced : IntegralSquareTorusCycle.DartListBalanced darts
  xWrap_eq : (darts.map ons_xWrapSign).sum = u.1
  yWrap_eq : (darts.map ons_yWrapSign).sum = u.2


end
end StatMech.FrontierD
