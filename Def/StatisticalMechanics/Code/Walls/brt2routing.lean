/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brt2routing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfxtrifexist
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def brt2_PosRouting (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ) : Prop :=
  0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
    ∃ (G : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d),
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        ((fun ω => forceOpenFinset G ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃)


end StatMech.Walls
