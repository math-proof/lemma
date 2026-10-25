/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
import Def.StatisticalMechanics.Code.Inequalities.ReimerButterflyMonoRefute
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace


lemma refuteW_nonneg : ∀ i b, 0 ≤ refuteW i b := fun _ _ => by norm_num [refuteW]

lemma refuteW_prob : ∀ i, refuteW i false + refuteW i true = 1 := fun _ => by norm_num [refuteW]


end StatMech
