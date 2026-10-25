/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bptpartitioncount.Part2
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


def bgn_idx (L : ℕ) (x : Site d) : Site d := fun i => (x i + L) / (2 * L + 1)


def bgn_Gn (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) : SimpleGraph (Site d) where
  Adj j k := j ≠ k ∧ ∃ a b : Site d, bgn_idx L a = j ∧ bgn_idx L b = k ∧ (openSubgraph d ω).Adj a b
  symm := by
    constructor
    rintro j k ⟨hjk, a, b, ha, hb, hab⟩
    exact ⟨hjk.symm, b, a, hb, ha, hab.symm⟩

end StatMech.Walls
