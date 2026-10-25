/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyMonoRefute
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace


noncomputable def refuteW : Fin 1 → Bool → ℝ := fun _ _ => (1 : ℝ) / 2

end StatMech
