module
public import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
public import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part91
open scoped BigOperators symmDiff
open MeasureTheory
set_option linter.style.longLine false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def finiteSupportCaseBudgetTotal {α κ : Type*}
    (Ω : Finset α) (caseOf : α → κ) (caseBudget : κ → ℝ) : ℝ :=
  let I : FinsetFiberIndex κ := { α := α, domain := Ω, map := caseOf }
  Finset.sum I.image (fun c => ((I.fiber c).card : ℝ) * caseBudget c)

end Exact3D
end StatMech
