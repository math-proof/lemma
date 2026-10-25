/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CriticalPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.FK.CriticalPoint
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


def fkSubcriticalSet (d : ℕ) (q : ℝ) : Set ℝ :=
  {p : ℝ | ∃ (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q), fkTheta d hp hp1 hq (q := q) = 0}

end FK
end StatMech
