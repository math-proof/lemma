/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Ising.IsingBoxSqueeze.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


def ibs_PlusBoundaryInfluence (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f ∈ pstc_cylinderBcfSet d, ∃ C : ℝ, ∀ n,
    |pstc_decayFun (fun n => plusMeasure d (φ n) β h) g f n|
      ≤ C * ibs_boundaryFraction d (φ n)


def ibs_MinusBoundaryInfluence (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f ∈ pstc_cylinderBcfSet d, ∃ C : ℝ, ∀ n,
    |pstc_decayFun (fun n => minusMeasure d (φ n) β h) g f n|
      ≤ C * ibs_boundaryFraction d (φ n)


end Ising
end StatMech
