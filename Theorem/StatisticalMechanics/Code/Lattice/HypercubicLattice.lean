/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.HypercubicLattice
open Set Finset


namespace StatMech

namespace Lattice

theorem nearestNeighbour_symm (d : ℕ) : Std.Symm (NearestNeighbour d) where
  symm x y h := by
    change (∑ i, (y i - x i).natAbs) = 1
    rw [← h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Int.natAbs_neg, neg_sub]

theorem nearestNeighbour_irrefl (d : ℕ) : Std.Irrefl (NearestNeighbour d) := by
  refine ⟨fun x h => ?_⟩
  simp only [NearestNeighbour, sub_self, Int.natAbs_zero, Finset.sum_const_zero] at h
  exact absurd h (by norm_num)


end Lattice
end StatMech
