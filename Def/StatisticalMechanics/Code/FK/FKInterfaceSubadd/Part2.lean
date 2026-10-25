/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketeData.Part2
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false


namespace StatMech

namespace FK

variable {d : ℕ}


def fis_UniformBoxSplit (d : ℕ) (t : ℝ) : Prop :=
  ∃ (C : ℝ) (κ : ℝ), 0 ≤ C ∧ κ ≠ 0 ∧
    (∀ m n, - Real.log (fkZ (boxGraph d (m + n)) (fsc_logistic t) 2)
        ≤ - Real.log (fkZ (boxGraph d m) (fsc_logistic t) 2)
          + - Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + C)
    ∧ BddBelow (Set.range fun n =>
        (- Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + C) / n)
    ∧ Tendsto (fun n => ((boxGraph d n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ)


end FK
end StatMech
