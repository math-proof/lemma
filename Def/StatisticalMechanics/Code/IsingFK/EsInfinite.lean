/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.MagNonneg.Part2
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.EsInfinite
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


noncomputable def fvMagnetization (d : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  ∫ ω, spin ω (origin d) ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d)))


end IsingFK
end StatMech
