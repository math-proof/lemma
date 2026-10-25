import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.IntegrandLimit.Part2
open MeasureTheory StatMech StatMech.Onsager


/--
[ons_gInt_pos_of_ne_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma ons_gInt_pos_of_ne_betaC_eq
  {β : ℝ}
  {k₁ k₂ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  0 < ons_gInt β k₁ k₂ := by
-- proof
  apply StatMech.Onsager.ons_gInt_pos_of_ne_betaC β hβ hcrit k₁ k₂

/--
[continuous_log_ons_gInt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma continuous_log_ons_gInt_eq
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  Continuous (fun p : ℝ × ℝ => Real.log (ons_gInt β p.1 p.2)) := by
-- proof
  apply StatMech.Onsager.continuous_log_ons_gInt β hβ hcrit

/--
[periodic_log_ons_gInt_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma periodic_log_ons_gInt_left_eq
  {β k₂ : ℝ} :
-- imply
  Function.Periodic (fun k₁ => Real.log (ons_gInt β k₁ k₂)) (2 * Real.pi) := by
-- proof
  apply StatMech.Onsager.periodic_log_ons_gInt_left β k₂

/--
[periodic_log_ons_gInt_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma periodic_log_ons_gInt_right_eq
  {β k₁ : ℝ} :
-- imply
  Function.Periodic (fun k₂ => Real.log (ons_gInt β k₁ k₂)) (2 * Real.pi) := by
-- proof
  apply StatMech.Onsager.periodic_log_ons_gInt_right β k₁

/--
[integral_log_ons_gInt_right_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma integral_log_ons_gInt_right_shift_eq
  {β k₁ : ℝ} :
-- imply
  (∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.log (ons_gInt β k₁ k₂)) = ∫ k₂ in (-Real.pi)..Real.pi, Real.log (ons_gInt β k₁ k₂) := by
-- proof
  apply StatMech.Onsager.integral_log_ons_gInt_right_shift β k₁

/--
[integral_log_ons_gInt_square_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma integral_log_ons_gInt_square_shift_eq
  {β : ℝ} :
-- imply
  (∫ k₁ in (0 : ℝ)..(2 * Real.pi), ∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.log (ons_gInt β k₁ k₂)) = ∫ k₁ in (-Real.pi)..Real.pi, ∫ k₂ in (-Real.pi)..Real.pi, Real.log (ons_gInt β k₁ k₂) := by
-- proof
  apply StatMech.Onsager.integral_log_ons_gInt_square_shift β

/--
[ons_log_gInt_riemann_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma ons_log_gInt_riemann_tendsto_eq
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  Filter.Tendsto (fun n : ℕ => (2 * Real.pi / n) ^ 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Real.log (ons_gInt β (2 * Real.pi * i / n) (2 * Real.pi * j / n))) Filter.atTop (nhds (∫ k₁ in (0 : ℝ)..(2 * Real.pi), ∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.log (ons_gInt β k₁ k₂))) := by
-- proof
  apply StatMech.Onsager.ons_log_gInt_riemann_tendsto β hβ hcrit

/--
[ons_log_gInt_density_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma ons_log_gInt_density_tendsto_eq
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  Filter.Tendsto (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Real.log (ons_gInt β (2 * Real.pi * i / n) (2 * Real.pi * j / n))) Filter.atTop (nhds (ons_freeEnergyIntegral β)) := by
-- proof
  apply StatMech.Onsager.ons_log_gInt_density_tendsto β hβ hcrit

/--
[ons_symbolDispersion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma ons_symbolDispersion_eq_eq
  {β k₁ k₂ : ℝ} :
-- imply
  ons_symbolDispersion β k₁ k₂ = ons_gInt β k₁ k₂ / Real.cosh β ^ 4 := by
-- proof
  apply StatMech.Onsager.ons_symbolDispersion_eq β k₁ k₂

/--
[ons_symbolDispersion_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma ons_symbolDispersion_pos_eq
  {β : ℝ}
  {k₁ k₂ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  0 < ons_symbolDispersion β k₁ k₂ := by
-- proof
  apply StatMech.Onsager.ons_symbolDispersion_pos β hβ hcrit k₁ k₂

/--
[log_ons_symbolDispersion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma log_ons_symbolDispersion_eq
  {β : ℝ}
  {k₁ k₂ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  Real.log (ons_symbolDispersion β k₁ k₂) = Real.log (ons_gInt β k₁ k₂) - 4 * Real.log (Real.cosh β) := by
-- proof
  apply StatMech.Onsager.log_ons_symbolDispersion β hβ hcrit k₁ k₂

/--
[ons_symbolDispersion_density_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma ons_symbolDispersion_density_tendsto_eq
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  Filter.Tendsto (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Real.log (ons_symbolDispersion β (2 * Real.pi * i / n) (2 * Real.pi * j / n))) Filter.atTop (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β))) := by
-- proof
  apply StatMech.Onsager.ons_symbolDispersion_density_tendsto β hβ hcrit

/--
[ons_log_gInt_density_shift_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma ons_log_gInt_density_shift_tendsto_eq
  {β : ℝ}
  {s t : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC)
  (hs : s ∈ Set.Icc (0 : ℝ) 1)
  (ht : t ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  Filter.Tendsto (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Real.log (ons_gInt β (2 * Real.pi * (i + s) / n) (2 * Real.pi * (j + t) / n))) Filter.atTop (nhds (ons_freeEnergyIntegral β)) := by
-- proof
  apply StatMech.Onsager.ons_log_gInt_density_shift_tendsto β hβ hcrit s t hs ht

/--
[ons_symbolDispersion_density_shift_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean)
-/
@[path]
private lemma ons_symbolDispersion_density_shift_tendsto_eq
  {β : ℝ}
  {s t : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC)
  (hs : s ∈ Set.Icc (0 : ℝ) 1)
  (ht : t ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  Filter.Tendsto (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Real.log (ons_symbolDispersion β (2 * Real.pi * (i + s) / n) (2 * Real.pi * (j + t) / n))) Filter.atTop (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β))) := by
-- proof
  apply StatMech.Onsager.ons_symbolDispersion_density_shift_tendsto β hβ hcrit s t hs ht


-- created on 2026-10-23
