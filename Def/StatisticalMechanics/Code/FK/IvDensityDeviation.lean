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
import Theorem.StatisticalMechanics.Code.FK.IvDensityDeviation
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


noncomputable def ivd_wiredOpenCountGeProb (d n : ℕ) (p : ℝ) (s : ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter
      (fun ω : ConfigSpace (Sym2 (boxVerts d n)) => s ≤ (chOpenCount (boxGraph d n) ω : ℝ)),
    wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω


end FK
end StatMech
