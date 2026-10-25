/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.ForestColouringClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Def.StatisticalMechanics.Code.Percolation.ThreeArmCoverClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


@[simp] theorem tac_plus_mk (x y : Site 2) :
    tac_plus s(x, y) = ((decide (x 1 = 0 ∧ y 1 = 0)) || (decide (x 0 = 0 ∧ y 0 = 0))) := rfl


theorem tac_isOpenEdge_iff (x y : Site 2) :
    IsOpenEdge 2 tac_plus x y ↔
      (hypercubicLattice 2).Adj x y ∧ ((x 1 = 0 ∧ y 1 = 0) ∨ (x 0 = 0 ∧ y 0 = 0)) := by
  unfold IsOpenEdge
  rw [tac_plus_mk]
  simp [Bool.or_eq_true, decide_eq_true_eq]


end Percolation
end StatMech
