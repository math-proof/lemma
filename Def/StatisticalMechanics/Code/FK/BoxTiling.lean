/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice SimpleGraph

variable {d : ℕ}


noncomputable def bxt_u (d : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  - Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2)


noncomputable def bxt_E (d n : ℕ) : ℝ := ((boxGraph d n).edgeFinset.card : ℝ)


end FK
end StatMech
