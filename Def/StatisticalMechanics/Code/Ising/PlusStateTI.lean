/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Ising.AeTailInvariantClose.Part2
import Theorem.StatisticalMechanics.Code.FK.FKErgodicFull.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


noncomputable def pst_plusShiftedFinite (β h : ℝ) (g : Multiplicative (Site d)) (n : ℕ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  (plusMeasure d n β h).map (continuous_shift g).measurable.aemeasurable


noncomputable def pst_minusShiftedFinite (β h : ℝ) (g : Multiplicative (Site d)) (n : ℕ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  (minusMeasure d n β h).map (continuous_shift g).measurable.aemeasurable


end Ising
end StatMech
