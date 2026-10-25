/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bclclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bpt2corridors.Part4
import Theorem.StatisticalMechanics.Code.Walls.bfc2indep
import Theorem.StatisticalMechanics.Code.Walls.bdecdecouple
import Theorem.StatisticalMechanics.Code.Walls.bfxtrifexist
import Theorem.StatisticalMechanics.Code.Walls.bclclose
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


def bcl_ArmResidue (p : ℝ≥0) (hp1 : p ≤ 1) : Prop :=
  ∀ n : ℕ,
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
      ∃ (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) (η₀ : ConfigSpace ↥I),
        (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
          (hypercubicLattice 2).Adj 0 a₃) ∧
        (∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
          Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧
            Connected 2 (removeSite 0 ω) a₃ x₃) ∧
        MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) ∧
        0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)


end StatMech.Walls
