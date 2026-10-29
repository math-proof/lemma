/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem reimer_wprob_core_of_perOrbitCard (h : PerOrbitCardAll) : ReimerWprobCore :=
  r2k_reimer_wprob_core_of_swapInjection
    (fun n A B => r2k_swapInjection_of_perOrbitCard A B (h n A B))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in

theorem reimer_inequality_of_perOrbitCard (h : PerOrbitCardAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : NNReal} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (reimer_wprob_core_of_perOrbitCard h) hp A B

end StatMech
