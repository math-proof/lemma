/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcl2close.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcorcorridors.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Walls.binsinsertion.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


def bins_ShellExtEvent (n : ℕ) (v₁ v₂ v₃ u₁ u₂ u₃ : Site 2) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | (v₁ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₁ u₁) ∧
    (v₂ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₂ u₂) ∧
    (v₃ ∈ box 2 n ∧ (hypercubicLattice 2).Adj v₃ u₃) ∧
    ω ∈ bins_ExtEvent (bondFinsetTouch 2 n) u₁ u₂ u₃}

end StatMech.Walls
