/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTI.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexUncond
import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


noncomputable def pstc_coordCM (x : Site d) : C(ConfigSpace (Site d), ℝ) :=
  ⟨fun ω => if ω x then (1 : ℝ) else 0,
    (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (ConfigSpace.continuous_eval x)⟩

end Ising
end StatMech
