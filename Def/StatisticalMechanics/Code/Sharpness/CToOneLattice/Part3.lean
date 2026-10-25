/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Instance.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part3
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


noncomputable def sctBoxInclusionEquiv (d : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    sctBox d n ≃ {z : sctBox d m // sctBoxInLarger d n m z} where
  toFun z := ⟨⟨z.1, fun i => le_trans (z.2 i) hnm⟩, z.2⟩
  invFun z := ⟨z.1.1, z.2⟩
  left_inv z := by ext i; rfl
  right_inv z := by ext i; rfl


end Sharpness
end StatMech
