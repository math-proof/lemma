/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWFourier
import Theorem.StatisticalMechanics.Code.Onsager.IntegrandLimit.Part2
import Def.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2


namespace StatMech.Onsager

theorem ons_spinDet_pos (L : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC)
    (a b : Fin 2) : 0 < ons_spinDet L β a b := by
  unfold ons_spinDet
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact ons_symbolDispersion_pos β hβ hcrit _ _

theorem log_ons_spinDet (L : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC)
    (a b : Fin 2) :
    Real.log (ons_spinDet L β a b) =
      ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
        Real.log (ons_symbolDispersion β
          (2 * Real.pi * (i + (a.val : ℝ) / 2) / L)
          (2 * Real.pi * (j + (b.val : ℝ) / 2) / L)) := by
  unfold ons_spinDet
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Real.log_prod]
    intro j hj
    exact ne_of_gt (ons_symbolDispersion_pos β hβ hcrit _ _)
  · intro i hi
    exact ne_of_gt (Finset.prod_pos fun j hj => ons_symbolDispersion_pos β hβ hcrit _ _)

theorem ons_halfShift_mem_Icc (a : Fin 2) : (a.val : ℝ) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · have ha : (a.val : ℝ) < 2 := by exact_mod_cast a.isLt
    linarith


theorem ons_spinDet_density_tendsto (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC)
    (a b : Fin 2) :
    Filter.Tendsto
      (fun L : ℕ => Real.log (ons_spinDet L β a b) / (2 * (L : ℝ) ^ 2))
      Filter.atTop
      (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β))) := by
  have ht := ons_symbolDispersion_density_shift_tendsto β hβ hcrit
    ((a.val : ℝ) / 2) ((b.val : ℝ) / 2)
    (ons_halfShift_mem_Icc a) (ons_halfShift_mem_Icc b)
  refine ht.congr' (Filter.eventually_atTop.2 ⟨1, fun L hL => ?_⟩)
  dsimp only
  rw [log_ons_spinDet L β hβ hcrit a b]
  ring

end StatMech.Onsager
