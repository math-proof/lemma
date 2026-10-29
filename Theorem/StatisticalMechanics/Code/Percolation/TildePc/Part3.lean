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
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part3
open MeasureTheory
open scoped NNReal
open Finset


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


@[simp]
theorem mem_tildePcSet {d : ℕ} {p : NNReal} :
    p ∈ tildePcSet d ↔
      ∃ hp : p ≤ 1, ∃ S : Finset (Site d), origin d ∈ S ∧ phi d p hp S < 1 :=
  Iff.rfl


end Percolation
end StatMech
