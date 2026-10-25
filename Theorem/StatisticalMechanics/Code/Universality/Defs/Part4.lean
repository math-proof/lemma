/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.Universality.Defs.Part3
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


theorem PositivelyAssociated.symm {E : Type*} {μ : Measure (ConfigSpace E)}
    (h : PositivelyAssociated μ) (A B : Set (ConfigSpace E))
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    μ.real B * μ.real A ≤ μ.real (B ∩ A) := by
  rw [mul_comm, Set.inter_comm]
  exact h A B hA hB


theorem PositivelyAssociated.sq_le_self {E : Type*} {μ : Measure (ConfigSpace E)}
    (h : PositivelyAssociated μ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    μ.real A * μ.real A ≤ μ.real A := by
  have key := h A A hA hA
  rwa [Set.inter_self] at key


end Universality
end StatMech
