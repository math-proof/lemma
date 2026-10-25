/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
import Instance.StatisticalMechanics.Code.Ising.InfiniteVolume.Part3
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def fvProbabilityMeasure (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  ⟨fvMeasure η n B β h, fvMeasure_isProbabilityMeasure η n B β h⟩


def plusField (d : ℕ) : ConfigSpace (Site d) := fun _ => true


def minusField (d : ℕ) : ConfigSpace (Site d) := fun _ => false


noncomputable def plusMeasure (d n : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (plusField d) n (bondFinsetTouch d n) β h


noncomputable def minusMeasure (d n : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (minusField d) n (bondFinsetTouch d n) β h


noncomputable def freeMeasure (d n : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (minusField d) n (bondFinsetInternal d n) β h


def InfiniteVolumeState (ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (μ : ProbabilityMeasure (ConfigSpace (Site d))) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeakConvergesTo (ρ ∘ φ) μ


end Ising
end StatMech
