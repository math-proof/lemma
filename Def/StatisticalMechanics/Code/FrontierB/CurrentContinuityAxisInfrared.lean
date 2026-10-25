/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAxisInfrared.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSparseGreenDecay
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusEmbedding.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFreeLeftContinuous
import Theorem.StatisticalMechanics.Code.FrontierB.MixedCurrentAxisPersistence.Part2
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierB

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

open StatMech.Percolation StatMech.Sharpness

variable {d : Nat}

noncomputable def boxFinsetEquiv (d n : Nat) :
    sctBox d n ≃ {x // x ∈ Ising.boxFinset d n} where
  toFun x := ⟨x.1, Ising.mem_boxFinset.mpr x.2⟩
  invFun x := ⟨x.1, Ising.mem_boxFinset.mp x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

end StatMech.FrontierB
