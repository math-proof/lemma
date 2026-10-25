/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniqPerEdge.Part3
import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def cfe_centered (q : ℝ) (t : ℝ) : ℝ :=
  ivp2_tiltFreeEnergy G q t - ivp2_tiltFreeEnergy G q 0

end FK
end StatMech
