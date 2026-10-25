/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTI.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexUncond
import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part5
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


def pstc_PlusCylinderDecay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f ∈ pstc_cylinderBcfSet d,
    Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g f) atTop (𝓝 0)


def pstc_MinusCylinderDecay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f ∈ pstc_cylinderBcfSet d,
    Tendsto (pstc_decayFun (fun n => minusMeasure d (φ n) β h) g f) atTop (𝓝 0)


end Ising
end StatMech
