/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredRootReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part8
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

theorem isingReflectedCenteredRadialGridCellPoint_center
    (n : Nat) (hn : 0 < n) (mesh : Real) :
    isingReflectedCenteredRadialGridCellPoint mesh n (n - 1) (n - 1)
        (1 / 2) (1 / 2) = 0 := by
  rw [isingReflectedCenteredRadialGridCellPoint_eq,
    isingReflectedCenteredRadialGridPosition_eq]
  push_cast [Nat.cast_sub (by omega : 1 <= n)]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp [Complex.mul_re, Complex.mul_im]


end
end StatMech.Universality
