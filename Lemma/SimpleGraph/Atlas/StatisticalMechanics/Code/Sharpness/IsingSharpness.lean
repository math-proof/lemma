import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
open Finset Real StatMech StatMech.Sharpness StatMech.Sharpness.IsingSharp


/--
[susceptibility_fixed_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpness.lean)
-/
@[path]
private lemma susceptibility_fixed_point_eq
  {S φ χ : ℝ}
-- given
  (hφ1 : φ < 1)
  (hself : χ ≤ S + φ * χ) :
-- imply
  χ ≤ S / (1 - φ) := by
-- proof
  apply StatMech.Sharpness.IsingSharp.susceptibility_fixed_point hφ1 hself

/--
[finite_susceptibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpness.lean)
-/
@[path]
private lemma finite_susceptibility_eq
  {origin : V}
  {corr : V → V → ℝ}
  {cardS : ℕ}
  {φ : ℝ}
-- given
  (hcorr_nonneg : ∀ x z, 0 ≤ corr x z)
  (hφ0 : 0 ≤ φ)
  (hφ1 : φ < 1)
  (hsimon : ∀ Λ : Finset V, (∑ z ∈ Λ, corr origin z) ≤ (cardS : ℝ) + φ * ((cardS : ℝ) / (1 - φ))) :
-- imply
  Summable (corr origin) ∧ (∑' x, corr origin x) ≤ (cardS : ℝ) / (1 - φ) := by
-- proof
  apply StatMech.Sharpness.IsingSharp.finite_susceptibility origin corr hcorr_nonneg cardS φ hφ0 hφ1 hsimon

/--
[geometric_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpness.lean)
-/
@[path]
private lemma geometric_decay_eq
  {L : ℕ}
  {φ : ℝ}
  {f : ℕ → ℝ}
-- given
  (hL : 1 ≤ L)
  (hφ0 : 0 ≤ φ)
  (hf0 : ∀ r, 0 ≤ f r)
  (hf1 : ∀ r, f r ≤ 1)
  (hstep : ∀ r, L < r → f r ≤ φ * f (r - L)) :
-- imply
  ∀ r, f r ≤ φ ^ ((r - 1) / L) := by
-- proof
  apply StatMech.Sharpness.IsingSharp.geometric_decay L hL φ hφ0 f hf0 hf1 hstep

/--
[geometric_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpness.lean)
-/
@[path]
private lemma geometric_le_exp_eq
  {L : ℕ}
  {φ : ℝ}
  {r : ℕ}
-- given
  (hL : 1 ≤ L)
  (hpos : 0 < φ)
  (hφ1 : φ < 1) :
-- imply
  φ ^ ((r - 1) / L) ≤ (1 / φ) * Real.exp ((Real.log φ / L) * r) := by
-- proof
  apply StatMech.Sharpness.IsingSharp.geometric_le_exp L hL φ hpos hφ1 r

/--
[exponential_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpness.lean)
-/
@[path]
private lemma exponential_decay_eq
  {L : ℕ}
  {φ : ℝ}
  {f : ℕ → ℝ}
-- given
  (hL : 1 ≤ L)
  (hpos : 0 < φ)
  (hφ1 : φ < 1)
  (hf0 : ∀ r, 0 ≤ f r)
  (hf1 : ∀ r, f r ≤ 1)
  (hstep : ∀ r, L < r → f r ≤ φ * f (r - L)) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ r : ℕ, f r ≤ C * Real.exp (-c * r) := by
-- proof
  apply StatMech.Sharpness.IsingSharp.exponential_decay L hL φ hpos hφ1 f hf0 hf1 hstep

/--
[meanfield_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpness.lean)
-/
@[path]
private lemma meanfield_bound_eq
  {β₀ : ℝ}
  {m : ℝ → ℝ}
  {β : ℝ}
-- given
  (hβ₀ : 0 < β₀)
  (hdiff : ∀ β ∈ Set.Ici β₀, DifferentiableAt ℝ (fun β => (m β) ^ 2) β)
  (hineq : ∀ β ∈ Set.Ioi β₀, (2 / β) * (1 - (m β) ^ 2) ≤ deriv (fun β => (m β) ^ 2) β)
  (hzero : m β₀ = 0)
  (hnonneg : ∀ β ∈ Set.Ici β₀, 0 ≤ m β)
  (hβ : β₀ ≤ β) :
-- imply
  Real.sqrt (1 - (β₀ / β) ^ 2) ≤ m β := by
-- proof
  apply StatMech.Sharpness.IsingSharp.meanfield_bound β₀ hβ₀ m hdiff hineq hzero hnonneg hβ

/--
[ising_sharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpness.lean)
-/
@[path]
private lemma ising_sharpness_eq
  {origin : V}
  {β_c : ℝ}
  {m : ℝ → ℝ}
  {corr : V → V → ℝ}
  {cardS : ℕ}
  {φ : ℝ}
-- given
  (hβc : 0 < β_c)
  (hdiff : ∀ β ∈ Set.Ici β_c, DifferentiableAt ℝ (fun β => (m β) ^ 2) β)
  (hineq : ∀ β ∈ Set.Ioi β_c, (2 / β) * (1 - (m β) ^ 2) ≤ deriv (fun β => (m β) ^ 2) β)
  (hzero : m β_c = 0)
  (hmnonneg : ∀ β ∈ Set.Ici β_c, 0 ≤ m β)
  (hcorr_nonneg : ∀ x z, 0 ≤ corr x z)
  (hφ0 : 0 ≤ φ)
  (hφ1 : φ < 1)
  (hsimon : ∀ Λ : Finset V, (∑ z ∈ Λ, corr origin z) ≤ (cardS : ℝ) + φ * ((cardS : ℝ) / (1 - φ))) :
-- imply
  (∀ β, β_c < β → Real.sqrt (1 - (β_c / β) ^ 2) ≤ m β) ∧ (Summable (corr origin) ∧ (∑' x, corr origin x) ≤ (cardS : ℝ) / (1 - φ)) := by
-- proof
  apply StatMech.Sharpness.IsingSharp.ising_sharpness origin β_c hβc m corr hdiff hineq hzero hmnonneg hcorr_nonneg cardS φ hφ0 hφ1 hsimon


-- created on 2026-10-23
