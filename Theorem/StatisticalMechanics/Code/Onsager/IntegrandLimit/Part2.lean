/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalPoint
import Theorem.StatisticalMechanics.Code.Onsager.FreeEnergy
import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodic2D
import Theorem.StatisticalMechanics.Code.Onsager.SymbolDet
import Def.StatisticalMechanics.Code.Onsager.IntegrandLimit
open scoped Real
open MeasureTheory


namespace StatMech.Onsager

theorem ons_symbolDispersion_eq (β k₁ k₂ : ℝ) :
    ons_symbolDispersion β k₁ k₂ = ons_gInt β k₁ k₂ / Real.cosh β ^ 4 := by
  exact ons_dispersion_cosh β (Real.cos k₁ + Real.cos k₂)

theorem ons_symbolDispersion_pos (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC)
    (k₁ k₂ : ℝ) : 0 < ons_symbolDispersion β k₁ k₂ := by
  rw [ons_symbolDispersion_eq]
  exact div_pos (ons_gInt_pos_of_ne_betaC β hβ hcrit k₁ k₂)
    (pow_pos (Real.cosh_pos β) 4)


theorem log_ons_symbolDispersion (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC)
    (k₁ k₂ : ℝ) :
    Real.log (ons_symbolDispersion β k₁ k₂) =
      Real.log (ons_gInt β k₁ k₂) - 4 * Real.log (Real.cosh β) := by
  rw [ons_symbolDispersion_eq, Real.log_div
    (ne_of_gt (ons_gInt_pos_of_ne_betaC β hβ hcrit k₁ k₂))
    (pow_ne_zero 4 (Real.cosh_pos β).ne'), Real.log_pow]
  norm_num


theorem ons_symbolDispersion_density_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (hcrit : β ≠ ons_betaC) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          Real.log (ons_symbolDispersion β
            (2 * Real.pi * i / n) (2 * Real.pi * j / n)))
      Filter.atTop
      (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β))) := by
  have ht := (ons_log_gInt_density_tendsto β hβ hcrit).sub_const
    (2 * Real.log (Real.cosh β))
  refine ht.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp_rw [log_ons_symbolDispersion β hβ hcrit, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hn0]
  ring


theorem ons_log_gInt_density_shift_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (hcrit : β ≠ ons_betaC) (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          Real.log (ons_gInt β
            (2 * Real.pi * (i + s) / n) (2 * Real.pi * (j + t) / n)))
      Filter.atTop (nhds (ons_freeEnergyIntegral β)) := by
  have hR := ons_riemann_periodic_two_shift
    (fun k₁ k₂ => Real.log (ons_gInt β k₁ k₂))
    (continuous_log_ons_gInt β hβ hcrit)
    (fun k₂ => periodic_log_ons_gInt_left β k₂) s t hs ht
  let c : ℝ := 1 / (8 * Real.pi ^ 2)
  have hscaled := hR.const_mul c
  have hlim : c *
      (∫ k₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.log (ons_gInt β k₁ k₂)) =
      ons_freeEnergyIntegral β := by
    rw [integral_log_ons_gInt_square_shift]
    rfl
  rw [hlim] at hscaled
  refine hscaled.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp [c]
  field_simp [hn0, Real.pi_ne_zero]
  ring


theorem ons_symbolDispersion_density_shift_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (hcrit : β ≠ ons_betaC) (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          Real.log (ons_symbolDispersion β
            (2 * Real.pi * (i + s) / n) (2 * Real.pi * (j + t) / n)))
      Filter.atTop
      (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β))) := by
  have htend := (ons_log_gInt_density_shift_tendsto β hβ hcrit s t hs ht).sub_const
    (2 * Real.log (Real.cosh β))
  refine htend.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp_rw [log_ons_symbolDispersion β hβ hcrit, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hn0]
  ring

end StatMech.Onsager
