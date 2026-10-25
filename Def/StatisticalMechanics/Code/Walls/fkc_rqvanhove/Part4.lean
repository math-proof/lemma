/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbdd.Part2
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbulkfraction
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqvanhove.Part3
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


noncomputable def fkc_g (d : ℕ) (s q : ℝ) (m : ℕ) : ℝ :=
  (2 * (m : ℝ) / (2 * m + 1)) * fkc_f d s q m
    + (1 - 2 * (m : ℝ) / (2 * m + 1)) * (-Real.log (1 - fsc_logistic s))


end StatMech.Walls
