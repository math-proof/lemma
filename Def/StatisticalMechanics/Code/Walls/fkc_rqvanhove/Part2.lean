/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbdd.Part2
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbulkfraction
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqvanhove
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


def fkc_AdditiveDoublingBound (d : ℕ) (s q : ℝ) : Prop :=
  ∃ I : ℕ → ℝ,
    (∀ j, 0 ≤ I j)
    ∧ Summable (fun j => I j / agl_E d (agl_K (j + 1)))
    ∧ (∀ j, fkc_u d s q (agl_K (j + 1))
        ≤ (2 : ℝ) ^ d * fkc_u d s q (agl_K j)
          + I j * (-Real.log (1 - fsc_logistic s)))
    ∧ (∀ j, |(2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))| ≤ I j)


end StatMech.Walls
