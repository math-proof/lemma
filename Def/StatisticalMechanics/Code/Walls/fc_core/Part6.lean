module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
public import Theorem.StatisticalMechanics.Code.Walls.fc_weightle
public import Theorem.StatisticalMechanics.Code.Walls.fc_allclosed
public import Theorem.StatisticalMechanics.Code.Walls.fc_bulkfraction
public import Theorem.StatisticalMechanics.Code.Walls.fc_core.Part6
open scoped BigOperators
open SimpleGraph Filter Topology Set
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.FK StatMech.Lattice


variable {d : ℕ}


noncomputable def fc_g (d : ℕ) (q : ℝ) (s : ℝ) (m : ℕ) : ℝ :=
  (2 * (m : ℝ) / (2 * m + 1)) * fc_f d q s m
    + (1 - 2 * (m : ℝ) / (2 * m + 1)) * (-Real.log (1 - fsc_logistic s))


end Walls
end StatMech
