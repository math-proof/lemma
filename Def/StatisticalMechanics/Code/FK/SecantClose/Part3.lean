/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.PressureDiff
import Theorem.StatisticalMechanics.Code.FK.TiltSecant.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part2
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


noncomputable def fsc_softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)


end FK
end StatMech
