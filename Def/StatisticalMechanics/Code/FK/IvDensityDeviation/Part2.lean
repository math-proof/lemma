/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityDeviationFull.Part2
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.AvgDensityCollapse
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.IvDensityDeviation.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


noncomputable def ivd_freeAvgDensity (d n : ℕ) (p : ℝ) : ℝ :=
  (∑ e ∈ (boxGraph d n).edgeFinset, freeEdgeDensity d 2 (edgeIncl d n e) p)
    / ((boxGraph d n).edgeFinset.card : ℝ)


noncomputable def ivd_wiredAvgDensity (d n : ℕ) (p : ℝ) : ℝ :=
  (∑ e ∈ (boxGraph d n).edgeFinset, wiredEdgeDensity d 2 (edgeIncl d n e) p)
    / ((boxGraph d n).edgeFinset.card : ℝ)


end FK
end StatMech
