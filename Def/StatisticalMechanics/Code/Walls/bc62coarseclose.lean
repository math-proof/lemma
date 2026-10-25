/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc61coarsebox.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc62_CoarseTrifPrecursor (d L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (b₁ ∈ bc61_boxAround d L 0 ∧ b₂ ∈ bc61_boxAround d L 0 ∧ b₃ ∈ bc61_boxAround d L 0) ∧
    ((hypercubicLattice d).Adj b₁ a₁ ∧ (hypercubicLattice d).Adj b₂ a₂ ∧
      (hypercubicLattice d).Adj b₃ a₃) ∧
    ((cluster d (removeSites (bc61_boxAround d L 0) ω) a₁).Infinite ∧
      (cluster d (removeSites (bc61_boxAround d L 0) ω) a₂).Infinite ∧
      (cluster d (removeSites (bc61_boxAround d L 0) ω) a₃).Infinite) ∧
    (¬ Connected d (removeSites (bc61_boxAround d L 0) ω) a₁ a₂ ∧
      ¬ Connected d (removeSites (bc61_boxAround d L 0) ω) a₁ a₃ ∧
      ¬ Connected d (removeSites (bc61_boxAround d L 0) ω) a₂ a₃)}


end StatMech.Walls
