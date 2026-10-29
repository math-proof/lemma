/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcl2close.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bclclose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcl2close
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


def bcl2_Bridge (p : NNReal) (hp1 : p ≤ 1) : Prop :=
  ∀ (m : ℕ) (x y z : Site 2),
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bxp_tripleEvent 2 m x y z) →
      ∃ (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ : Site 2) (η₀ : ConfigSpace ↥I),
        (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
          (hypercubicLattice 2).Adj 0 a₃) ∧
        (∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
          Connected 2 (removeSite 0 ω) a₁ x ∧ Connected 2 (removeSite 0 ω) a₂ y ∧
            Connected 2 (removeSite 0 ω) a₃ z) ∧
        MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x y z) ∧
        0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (bpt2_Ext I a₁ a₂ a₃ x y z)


end StatMech.Walls
