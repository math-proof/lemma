/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbdd.Part2
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbulkfraction
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


noncomputable def fkc_u (d : ℕ) (s q : ℝ) (n : ℕ) : ℝ :=
  -Real.log (ecz_fkZEdge (boxGraph d n) (fsc_logistic s) q)


noncomputable def fkc_f (d : ℕ) (s q : ℝ) (n : ℕ) : ℝ :=
  fkc_u d s q n / ((boxGraph d n).edgeFinset.card : ℝ)


end StatMech.Walls
