/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketeData
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
  (Gn : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (Gn n).Adj]


variable {d : ℕ}


def bfd_FKInterfaceData (d : ℕ) (t : ℝ) : Prop :=
  ∃ (c : ℕ → ℝ) (κ : ℝ),
    Subadditive (fun n => - Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + c n)
    ∧ BddBelow (Set.range fun n =>
        (- Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + c n) / n)
    ∧ Tendsto (fun n => c n / n) atTop (𝓝 0)
    ∧ κ ≠ 0
    ∧ Tendsto (fun n => ((boxGraph d n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ)


end FK
end StatMech
