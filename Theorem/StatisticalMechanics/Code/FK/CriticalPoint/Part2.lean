module
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.Theta
public import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part2
open MeasureTheory
open scoped NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CriticalPoint.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


@[simp]
theorem mem_fkSubcriticalSet {d : ℕ} {q : ℝ} {p : ℝ} :
    p ∈ fkSubcriticalSet d q ↔
      ∃ (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q), fkTheta d hp hp1 hq (q := q) = 0 :=
  Iff.rfl


end FK
end StatMech
