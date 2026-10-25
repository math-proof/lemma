/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
import Def.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part4
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rpw_reimer_wprob_core_of_weightInjection (h : rpw_WeightInjectionAll) :
    ReimerWprobCore := by
  intro n φ hφ0 hφ1 A B
  exact rpw_reimer_wprob_of_weightInjection φ hφ0 hφ1 (h n A B)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rpw_reimer_inequality_of_weightInjection (h : rpw_WeightInjectionAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (rpw_reimer_wprob_core_of_weightInjection h) hp A B


end StatMech
