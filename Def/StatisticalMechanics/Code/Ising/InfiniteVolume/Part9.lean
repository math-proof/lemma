module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
public import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
public import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part8
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def plusState (d : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => plusMeasure d n β h)


noncomputable def minusState (d : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => minusMeasure d n β h)


noncomputable def freeState (d : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => freeMeasure d n β h)


end Ising
end StatMech
