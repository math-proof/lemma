/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.KramersWannier
open Real


namespace StatMech

namespace Ising

theorem sinh_two_dualTemp (β : ℝ) :
    Real.sinh (2 * dualTemp β) = 1 / Real.sinh (2 * β) := by
  unfold dualTemp
  rw [show (2 : ℝ) * ((1 / 2) * Real.arsinh (1 / Real.sinh (2 * β)))
        = Real.arsinh (1 / Real.sinh (2 * β)) by ring,
    Real.sinh_arsinh]


theorem kramersWannier_duality (β : ℝ) (hβ : 0 < β) :
    Real.sinh (2 * β) * Real.sinh (2 * dualTemp β) = 1 := by
  have hs : 0 < Real.sinh (2 * β) := by rw [Real.sinh_pos_iff]; linarith
  rw [sinh_two_dualTemp]
  field_simp


theorem dualTemp_pos (β : ℝ) (hβ : 0 < β) : 0 < dualTemp β := by
  have hs : 0 < Real.sinh (2 * β) := by rw [Real.sinh_pos_iff]; linarith
  unfold dualTemp
  have : 0 < Real.arsinh (1 / Real.sinh (2 * β)) := by
    rw [Real.arsinh_pos_iff]; positivity
  linarith


theorem dualTemp_involution (β : ℝ) (hβ : 0 < β) : dualTemp (dualTemp β) = β := by
  have hs : 0 < Real.sinh (2 * β) := by rw [Real.sinh_pos_iff]; linarith
  have hd : 0 < dualTemp β := dualTemp_pos β hβ
  have key : Real.sinh (2 * dualTemp (dualTemp β)) = Real.sinh (2 * β) := by
    rw [sinh_two_dualTemp, sinh_two_dualTemp]
    field_simp
  have := Real.sinh_injective key
  linarith


theorem dualTemp_fixed_iff (β : ℝ) (hβ : 0 < β) :
    dualTemp β = β ↔ Real.sinh (2 * β) = 1 := by
  have hs : 0 < Real.sinh (2 * β) := by rw [Real.sinh_pos_iff]; linarith
  have hiff : dualTemp β = β ↔ Real.sinh (2 * dualTemp β) = Real.sinh (2 * β) := by
    constructor
    · intro h; rw [h]
    · intro h; have := Real.sinh_injective h; linarith
  rw [hiff, sinh_two_dualTemp, eq_comm, eq_div_iff hs.ne', eq_comm]
  constructor
  · intro h; nlinarith [hs, h]
  · intro h; rw [h]; ring


end Ising
end StatMech
