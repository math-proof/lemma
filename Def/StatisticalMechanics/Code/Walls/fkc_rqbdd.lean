/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbdd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbdd
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


section FreeEnergy

noncomputable def fkc_edgeFreeEnergy (d : ℕ) (s q : ℝ) (n : ℕ) : ℝ :=
  Real.log (ecz_fkZEdge (boxGraph d n) (fsc_logistic s) q) / ((boxGraph d n).edgeFinset.card : ℝ)
    + Real.log (1 + Real.exp s)


end FreeEnergy
end StatMech.Walls
