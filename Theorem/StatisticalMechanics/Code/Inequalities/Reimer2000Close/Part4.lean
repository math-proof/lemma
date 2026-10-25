/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part4
import Def.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part4
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem r2k_reimer_wprob_core_of_swapInjection (h : r2k_SwapInjectionAll) : ReimerWprobCore := by
  intro n φ hφ0 hφ1 A B
  exact r2k_reimer_wprob_of_swapInjection φ hφ0 hφ1 (h n A B)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in

theorem r2k_reimer_inequality_of_swapInjection (h : r2k_SwapInjectionAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (r2k_reimer_wprob_core_of_swapInjection h) hp A B


end StatMech
