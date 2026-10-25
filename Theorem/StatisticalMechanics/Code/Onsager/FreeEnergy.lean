/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/FreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.Pressure.Part2
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Theorem.StatisticalMechanics.Code.Onsager.CriticalPoint
import Def.StatisticalMechanics.Code.Onsager.FreeEnergy


namespace StatMech.Onsager

open StatMech.Ising


theorem ons_torusPressure_eq (L : ℕ) [Fact (2 < L)] (β : ℝ) (hβ : 0 ≤ β) :
    ons_pressureFinite (onsTorusGraph L) β
      = Real.log 2 + 2 * Real.log (Real.cosh β)
        + Real.log (ons_X (onsTorusGraph L) (Real.tanh β)) / ((L : ℝ) ^ 2) := by
  have hV : 0 < Fintype.card (ZMod L × ZMod L) := by
    rw [onsTorus_card_verts]
    have hL : 0 < L := by have := (Fact.out : 2 < L); omega
    exact pow_pos hL 2
  rw [ons_pressureFinite_eq _ β hβ hV, onsTorus_card_edges, onsTorus_card_verts]
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Fact.out : 2 < L); omega)
  have hcoef : ((2 * L ^ 2 : ℕ) : ℝ) / ((L ^ 2 : ℕ) : ℝ) = 2 := by
    push_cast
    rw [mul_div_assoc, div_self (pow_ne_zero 2 hLne), mul_one]
  rw [hcoef]
  push_cast
  ring


theorem ons_free_energy_of_KacWardResidue
    (β : ℝ) (hβ : 0 ≤ β) (hres : ons_KacWardResidue β) :
    Filter.Tendsto
      (fun L : ℕ => if h : 2 < L then
          (letI : Fact (2 < L) := ⟨h⟩; ons_pressureFinite (onsTorusGraph L) β)
        else 0)
      Filter.atTop (nhds (ons_pressure β)) := by
  have hval : ons_pressure β
      = (Real.log 2 + 2 * Real.log (Real.cosh β))
        + (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β)) := by
    unfold ons_pressure; ring
  rw [hval]
  unfold ons_KacWardResidue at hres
  have htend := hres.const_add (Real.log 2 + 2 * Real.log (Real.cosh β))
  refine htend.congr' ?_
  refine Filter.eventually_atTop.2 ⟨3, fun L hL => ?_⟩
  have hLpos : 2 < L := by omega
  simp only [dif_pos hLpos]
  haveI : Fact (2 < L) := ⟨hLpos⟩
  rw [ons_torusPressure_eq L β hβ]

end StatMech.Onsager
