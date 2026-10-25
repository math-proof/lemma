/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.ABLatticeUnconditional
import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryLimit.Part2
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def abblLatticeCoupling (d : Nat) : Sym2 (Site d) → Real :=
  Sym2.lift ⟨fun x y ↦
    if (hypercubicLattice d).Adj x y then 1 else 0, by
      intro x y
      change (if (hypercubicLattice d).Adj x y then 1 else 0) =
        if (hypercubicLattice d).Adj y x then 1 else 0
      by_cases hxy : (hypercubicLattice d).Adj x y
      · rw [if_pos hxy, if_pos hxy.symm]
      · rw [if_neg hxy, if_neg (fun hyx ↦ hxy hyx.symm)]⟩

end Sharpness
end StatMech
