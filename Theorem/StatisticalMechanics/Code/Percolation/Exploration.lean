/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.Exploration
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


section Finite

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem w1_sum (p : NNReal) (hp : p ≤ 1) : (∑ b : Bool, w1 p hp b) = 1 := by
  have h : (∑ b : Bool, w1 p hp b) = (bernoulliMeasure p hp).real Set.univ := by
    simp only [w1]
    rw [← MeasureTheory.measureReal_biUnion_finset]
    · congr 1; ext x; simp
    · intro a _ b _ hab; simp only [Set.disjoint_singleton]; exact hab
    · intro a _; exact measurableSet_singleton a
  rw [h, probReal_univ]


end Finite
end Percolation
end StatMech
