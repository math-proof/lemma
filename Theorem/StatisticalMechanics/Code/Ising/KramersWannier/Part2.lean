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
import Def.StatisticalMechanics.Code.Ising.KramersWannier.Part2
open Real


namespace StatMech

namespace Ising

theorem selfDualPoint_pos : 0 < selfDualPoint := by
  unfold selfDualPoint
  have : 0 < Real.arsinh 1 := by rw [Real.arsinh_pos_iff]; norm_num
  linarith


theorem sinh_two_selfDualPoint : Real.sinh (2 * selfDualPoint) = 1 := by
  unfold selfDualPoint
  rw [show (2 : ℝ) * ((1 / 2) * Real.arsinh 1) = Real.arsinh 1 by ring, Real.sinh_arsinh]


theorem dualTemp_selfDualPoint : dualTemp selfDualPoint = selfDualPoint :=
  (dualTemp_fixed_iff selfDualPoint selfDualPoint_pos).mpr sinh_two_selfDualPoint


theorem selfDualPoint_eq_log : selfDualPoint = (1 / 2) * Real.log (1 + Real.sqrt 2) := by
  unfold selfDualPoint
  rw [Real.arsinh]
  norm_num


theorem exists_unique_selfDual : ∃! β : ℝ, 0 < β ∧ Real.sinh (2 * β) = 1 := by
  refine ⟨selfDualPoint, ⟨selfDualPoint_pos, sinh_two_selfDualPoint⟩, ?_⟩
  rintro y ⟨hy, hsy⟩
  have : Real.sinh (2 * y) = Real.sinh (2 * selfDualPoint) := by
    rw [hsy, sinh_two_selfDualPoint]
  have := Real.sinh_injective this
  linarith


theorem kramersWannier_critical (βc : ℝ) (hβc : 0 < βc) (hfix : dualTemp βc = βc) :
    Real.sinh (2 * βc) = 1 :=
  (dualTemp_fixed_iff βc hβc).mp hfix


theorem kramersWannier_critical_eq_log (βc : ℝ) (hβc : 0 < βc) (hfix : dualTemp βc = βc) :
    βc = (1 / 2) * Real.log (1 + Real.sqrt 2) := by
  have hsc : Real.sinh (2 * βc) = 1 := kramersWannier_critical βc hβc hfix
  have heq : Real.sinh (2 * βc) = Real.sinh (2 * selfDualPoint) := by
    rw [hsc, sinh_two_selfDualPoint]
  have := Real.sinh_injective heq
  rw [← selfDualPoint_eq_log]
  linarith

end Ising
end StatMech
