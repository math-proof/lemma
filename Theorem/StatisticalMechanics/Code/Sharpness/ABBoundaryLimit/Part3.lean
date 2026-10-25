/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.ABLatticeUnconditional
import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryLimit.Part2
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

@[simp] theorem abblLatticeCoupling_mk (d : Nat) (x y : Site d) :
    abblLatticeCoupling d s(x, y) =
      if (hypercubicLattice d).Adj x y then 1 else 0 := by
  simp [abblLatticeCoupling]

theorem abblLatticeCoupling_nonneg (d : Nat) (e : Sym2 (Site d)) :
    0 ≤ abblLatticeCoupling d e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [abblLatticeCoupling_mk]
      split <;> norm_num

theorem abblLatticeCoupling_support {d : Nat} (x y : Site d)
    (hxy : ¬ (hypercubicLattice d).Adj x y) :
    abblLatticeCoupling d s(x, y) = 0 := by
  rw [abblLatticeCoupling_mk, if_neg hxy]


end Sharpness
end StatMech
