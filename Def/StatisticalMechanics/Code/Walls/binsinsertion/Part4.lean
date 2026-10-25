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
import Theorem.StatisticalMechanics.Code.Walls.binsinsertion.Part4
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


def bins_NineShellEvent (n : ℕ) (v u : Fin 9 → Site 2) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | (∀ i, v i ∈ box 2 n ∧ (hypercubicLattice 2).Adj (v i) (u i)) ∧
    (∀ i, (cluster 2
      (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) (u i)).Infinite) ∧
    ∀ i j, i ≠ j →
      cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) (u i) ≠
      cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) (u j)}


end StatMech.Walls
