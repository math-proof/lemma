/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


noncomputable def horizWalk (c : ℤ) :
    (k : ℕ) → (a : ℤ) → (hypercubicLattice 2).Walk ![a, c] ![a + (k : ℤ), c]
  | 0, a => by
      simpa using (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk ![a, c] ![a, c])
  | k + 1, a => by
      have step : (hypercubicLattice 2).Adj ![a, c] ![a + 1, c] := latAdj_right a c
      have rest := horizWalk c k (a + 1)
      have he : (![a + 1 + (k : ℤ), c] : Site 2) = ![a + ((k + 1 : ℕ) : ℤ), c] := by
        funext i; fin_cases i <;> (simp; try ring)
      rw [he] at rest
      exact SimpleGraph.Walk.cons step rest


end FK
end StatMech
