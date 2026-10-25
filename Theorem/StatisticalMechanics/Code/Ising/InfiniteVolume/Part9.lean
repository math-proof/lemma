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
import Def.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem plusState_isInfiniteVolumeState (d : ℕ) (β h : ℝ) :
    InfiniteVolumeState (fun n => plusMeasure d n β h) (plusState d β h) :=
  limitState_isInfiniteVolumeState _


theorem minusState_isInfiniteVolumeState (d : ℕ) (β h : ℝ) :
    InfiniteVolumeState (fun n => minusMeasure d n β h) (minusState d β h) :=
  limitState_isInfiniteVolumeState _


theorem freeState_isInfiniteVolumeState (d : ℕ) (β h : ℝ) :
    InfiniteVolumeState (fun n => freeMeasure d n β h) (freeState d β h) :=
  limitState_isInfiniteVolumeState _

end Ising
end StatMech
