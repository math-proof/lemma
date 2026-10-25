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
import Theorem.StatisticalMechanics.Code.FK.PcUpperUncond.Part3
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


def FkNonPercolationBound (q : ℝ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : Prop :=
  1 - fkTheta 2 hp hp1 hq (q := q) ≤ fkPcUpperBound 2 p


end FK
end StatMech
