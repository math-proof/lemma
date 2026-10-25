/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc72quotient.Part3
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc73sublattice.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc73_mem_sublattice {L R : ℕ} {y : Site d} :
    y ∈ bc73_sublattice d L R ↔ y ∈ box d R ∧ bc73_onSublattice L y := by
  classical
  rw [bc73_sublattice, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]


theorem bc73_sublattice_pairwise_disjoint (L R : ℕ) :
    (bc73_sublattice d L R : Set (Site d)).Pairwise
      (fun y y' => Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y')) := by
  intro y hy y' hy' hne
  rw [Finset.mem_coe, bc73_mem_sublattice] at hy hy'
  exact bc73_sublattice_boxes_disjoint hy.2 hy'.2 hne


end StatMech.Walls
