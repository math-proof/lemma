/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

@[simp] theorem triangularIntStep_axisDirection (d : Fin 4) :
    triangularIntStep (triangularAxisDirection d) = stepOf d := by
  fin_cases d <;> rfl

theorem triangularPathDisplacement_map_axis (l : List (Fin 4)) :
    triangularPathDisplacement (l.map triangularAxisDirection) =
      ons_pathDisplacement l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, triangularPathDisplacement_cons,
        ons_pathDisplacement_cons, triangularIntStep_axisDirection, ih]

theorem triangularPathVertices_map_axis (l : List (Fin 4)) :
    triangularPathVertices (l.map triangularAxisDirection) =
      ons_pathVertices l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, triangularPathVertices_cons,
        ons_pathVertices_cons, triangularIntStep_axisDirection, ih]

end StatMech.FrontierA
