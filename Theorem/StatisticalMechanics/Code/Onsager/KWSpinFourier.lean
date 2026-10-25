/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Def.StatisticalMechanics.Code.Onsager.KWSpinFourier


namespace StatMech.Onsager

theorem ons_dirPhase_eq_zpow (u v : ℂ) (mu : Fin 4) :
    ons_dirPhase u v mu =
      u ^ ons_dirExponentX mu * v ^ ons_dirExponentY mu := by
  fin_cases mu <;> simp [ons_dirPhase, ons_dirExponentX, ons_dirExponentY]

theorem prod_same_zpow {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (u : ℂ) (hu : u ≠ 0) (f : alpha → ℤ) :
    (∏ i ∈ s, u ^ f i) = u ^ (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      exact (zpow_add₀ hu _ _).symm

theorem prod_ons_dirPhase {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (d : alpha → Fin 4) :
    (∏ i, ons_dirPhase u v (d i)) =
      u ^ (∑ i, ons_dirExponentX (d i)) *
        v ^ (∑ i, ons_dirExponentY (d i)) := by
  rw [← prod_same_zpow Finset.univ u hu (fun i => ons_dirExponentX (d i)),
    ← prod_same_zpow Finset.univ v hv (fun i => ons_dirExponentY (d i)),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact ons_dirPhase_eq_zpow u v (d i)


end StatMech.Onsager
