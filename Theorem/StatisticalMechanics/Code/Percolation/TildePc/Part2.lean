/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TildePc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part2
open MeasureTheory
open scoped NNReal
open Finset


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem phi_nonneg (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d)) :
    0 ≤ phi d p hp S := by
  unfold phi
  refine mul_nonneg p.coe_nonneg (Finset.sum_nonneg ?_)
  intro e _
  exact connWithinProb_nonneg d p hp S e.1


end Percolation
end StatMech
