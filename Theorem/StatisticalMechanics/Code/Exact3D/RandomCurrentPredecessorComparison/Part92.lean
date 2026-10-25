/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part84
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal {α κ : Type*}
    (Ω : Finset α) (caseOf : α → κ) (caseBudget : κ → ℝ) :
    Finset.sum Ω (fun a => caseBudget (caseOf a)) =
      finiteSupportCaseBudgetTotal Ω caseOf caseBudget := by
  classical
  let I : FinsetFiberIndex κ := { α := α, domain := Ω, map := caseOf }
  simpa [finiteSupportCaseBudgetTotal, I] using
    (FinsetFiberIndex.sum_fiber_weight I caseBudget)

set_option linter.style.longLine false in


theorem finset_sum_le_of_finiteSupportCaseBudgetTotal_le {α κ : Type*}
    (Ω : Finset α) (F : α → ℝ) (caseOf : α → κ)
    (caseBudget : κ → ℝ) {target : ℝ}
    (hpoint : ∀ a ∈ Ω, F a ≤ caseBudget (caseOf a))
    (htotal : finiteSupportCaseBudgetTotal Ω caseOf caseBudget ≤ target) :
    Finset.sum Ω F ≤ target := by
  calc
    Finset.sum Ω F ≤ Finset.sum Ω (fun a => caseBudget (caseOf a)) :=
      Finset.sum_le_sum hpoint
    _ = finiteSupportCaseBudgetTotal Ω caseOf caseBudget :=
      finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal Ω caseOf
        caseBudget
    _ ≤ target := htotal

end Exact3D
end StatMech
