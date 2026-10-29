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
import Def.StatisticalMechanics.Code.Percolation.TildePc
open MeasureTheory
open scoped NNReal
open Finset


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem connWithinProb_nonneg (d : ℕ) (p : NNReal) (hp : p ≤ 1) (S : Finset (Site d))
    (x : Site d) : 0 ≤ connWithinProb d p hp S x := by
  classical
  unfold connWithinProb
  split
  · split
    · exact ENNReal.toReal_nonneg
    · exact le_refl 0
  · exact le_refl 0


end Percolation
end StatMech
