/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTI.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexUncond
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


noncomputable def pstc_decayFun (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (f : (ConfigSpace (Site d)) →ᵇ ℝ) (n : ℕ) : ℝ :=
  (∫ x, f x ∂(μ n : Measure _)) - (∫ x, f (shift g x) ∂(μ n : Measure _))


end Ising
end StatMech
