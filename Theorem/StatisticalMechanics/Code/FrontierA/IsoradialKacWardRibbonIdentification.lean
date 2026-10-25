/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


theorem sum_boolOrientations_eq_prod_formanCycleCoefficient
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (holonomy : Component -> Complex) :
    (∑ orientation : Component -> Bool,
        ∏ component : Component,
          if orientation component then 1 - holonomy component
          else 1 - (holonomy component)⁻¹) =
      ∏ component : Component,
        formanCycleCoefficient (holonomy component) := by
  calc
    (∑ orientation : Component -> Bool,
        ∏ component : Component,
          if orientation component then 1 - holonomy component
          else 1 - (holonomy component)⁻¹) =
      ∏ component : Component,
        ∑ orientation : Bool,
          if orientation then 1 - holonomy component
          else 1 - (holonomy component)⁻¹ :=
      (Fintype.prod_sum fun (component : Component) (orientation : Bool) =>
        if orientation then 1 - holonomy component
        else 1 - (holonomy component)⁻¹).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro component _
      simp [formanCycleCoefficient]
      ring


end StatMech.FrontierA
