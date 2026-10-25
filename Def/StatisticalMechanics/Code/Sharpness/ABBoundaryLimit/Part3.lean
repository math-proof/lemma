/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.ABLatticeUnconditional
import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryLimit.Part3
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def abblBoxEquiv (d n : Nat) :
    sctBox d n ≃ ↑(ablBoxFinset d n) where
  toFun x := ⟨x.1, mem_ablBoxFinset.mpr x.2⟩
  invFun x := ⟨x.1, mem_ablBoxFinset.mp x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

end Sharpness
end StatMech
