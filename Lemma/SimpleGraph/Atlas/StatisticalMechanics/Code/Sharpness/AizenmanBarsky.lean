import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.AizenmanBarsky.Part2
open Set Real Filter Topology StatMech StatMech.Sharpness


/--
[ab_inequality_implies_eq12](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean)
-/
@[path]
private lemma ab_inequality_implies_eq12_eq
  {M : ℝ → ℝ → ℝ}
  {J : ℝ}
-- given
  (hAB : AizenmanBarskyInequality M J)
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (heq6 : 1 - M β h ≤ β * deriv (fun β => M β h) β) :
-- imply
  1 - M β h ≤ (β * J) * (M β h * deriv (fun h => M β h) h) := by
-- proof
  apply StatMech.Sharpness.ab_inequality_implies_eq12 M J hAB β h hβ heq6

/--
[ab_field_sq_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean)
-/
@[path]
private lemma ab_field_sq_lower_bound_eq
  {K : ℝ}
  {m : ℝ → ℝ}
-- given
  (hK : 0 < K)
  (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ m h)
  (hmono : ∀ h ∈ Ici (0 : ℝ), 0 ≤ deriv m h)
  (hm0 : m 0 = 0)
  (heq12 : ∀ h ∈ Ici (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h))
  (h₀ : ℝ)
  (hh₀ : 0 < h₀)
  (hle : m h₀ ≤ 1 / 2) :
-- imply
  h₀ / K ≤ (m h₀) ^ 2 := by
-- proof
  apply StatMech.Sharpness.ab_field_sq_lower_bound K hK m hdiff hmono hm0 heq12 h₀ hh₀ hle

/--
[ab_field_sqrt_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean)
-/
@[path]
private lemma ab_field_sqrt_lower_bound_eq
  {K : ℝ}
  {m : ℝ → ℝ}
-- given
  (hK : 0 < K)
  (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ m h)
  (hmono : ∀ h ∈ Ici (0 : ℝ), 0 ≤ deriv m h)
  (hmnn : ∀ h, 0 ≤ m h)
  (hm0 : m 0 = 0)
  (heq12 : ∀ h ∈ Ici (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h))
  (h : ℝ)
  (hh : h ∈ Ioc (0 : ℝ) (K / 4)) :
-- imply
  Real.sqrt (h / K) ≤ m h := by
-- proof
  apply StatMech.Sharpness.ab_field_sqrt_lower_bound K hK m hdiff hmono hmnn hm0 heq12 h hh

/--
[ab_field_meanfield_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean)
-/
@[path]
private lemma ab_field_meanfield_bound_eq
  {K : ℝ}
  {m : ℝ → ℝ}
-- given
  (hK : 0 < K)
  (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ m h)
  (hmono : ∀ h ∈ Ici (0 : ℝ), 0 ≤ deriv m h)
  (hmnn : ∀ h, 0 ≤ m h)
  (hm0 : m 0 = 0)
  (heq12 : ∀ h ∈ Ici (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h)) :
-- imply
  ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (K / 4), c * Real.sqrt h ≤ m h := by
-- proof
  apply StatMech.Sharpness.ab_field_meanfield_bound K hK m hdiff hmono hmnn hm0 heq12

/--
[ab_perco_meanfield_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean)
-/
@[path]
private lemma ab_perco_meanfield_sqrt_eq
  {M : ℝ → ℝ → ℝ}
  {J : ℝ}
  {βc : ℝ}
-- given
  (hβc : 0 < βc)
  (hJ : 0 < J)
  (hAB : AizenmanBarskyInequality M J)
  (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun h => M βc h) h)
  (hmono : ∀ h ∈ Ici (0 : ℝ), 0 ≤ deriv (fun h => M βc h) h)
  (hmnn : ∀ h, 0 ≤ M βc h)
  (hm0 : M βc 0 = 0)
  (heq6 : ∀ h ∈ Ici (0 : ℝ), 1 - M βc h ≤ βc * deriv (fun β => M β h) βc) :
-- imply
  ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (βc * J / 4), c * Real.sqrt h ≤ M βc h := by
-- proof
  apply StatMech.Sharpness.ab_perco_meanfield_sqrt M J βc hβc hJ hAB hdiff hmono hmnn hm0 heq6

/--
[ab_field_sq_lower_bound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean)
-/
@[path]
private lemma ab_field_sq_lower_bound_pos_eq
  {K : ℝ}
  {m : ℝ → ℝ}
-- given
  (hK : 0 < K)
  (hdiff : ∀ h ∈ Ioi (0 : ℝ), DifferentiableAt ℝ m h)
  (hmono : ∀ h ∈ Ioi (0 : ℝ), 0 ≤ deriv m h)
  (hcont0 : ContinuousWithinAt m (Ici (0 : ℝ)) 0)
  (hm0 : m 0 = 0)
  (heq12 : ∀ h ∈ Ioi (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h))
  (h₀ : ℝ)
  (hh₀ : 0 < h₀)
  (hle : m h₀ ≤ 1 / 2) :
-- imply
  h₀ / K ≤ (m h₀) ^ 2 := by
-- proof
  apply StatMech.Sharpness.ab_field_sq_lower_bound_pos K hK m hdiff hmono hcont0 hm0 heq12 h₀ hh₀ hle

/--
[ab_field_sqrt_lower_bound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean)
-/
@[path]
private lemma ab_field_sqrt_lower_bound_pos_eq
  {K : ℝ}
  {m : ℝ → ℝ}
-- given
  (hK : 0 < K)
  (hdiff : ∀ h ∈ Ioi (0 : ℝ), DifferentiableAt ℝ m h)
  (hmono : ∀ h ∈ Ioi (0 : ℝ), 0 ≤ deriv m h)
  (hcont0 : ContinuousWithinAt m (Ici (0 : ℝ)) 0)
  (hmnn : ∀ h, 0 ≤ m h)
  (hm0 : m 0 = 0)
  (heq12 : ∀ h ∈ Ioi (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h))
  (h : ℝ)
  (hh : h ∈ Ioc (0 : ℝ) (K / 4)) :
-- imply
  Real.sqrt (h / K) ≤ m h := by
-- proof
  apply StatMech.Sharpness.ab_field_sqrt_lower_bound_pos K hK m hdiff hmono hcont0 hmnn hm0 heq12 h hh

/--
[ab_field_meanfield_bound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean)
-/
@[path]
private lemma ab_field_meanfield_bound_pos_eq
  {K : ℝ}
  {m : ℝ → ℝ}
-- given
  (hK : 0 < K)
  (hdiff : ∀ h ∈ Ioi (0 : ℝ), DifferentiableAt ℝ m h)
  (hmono : ∀ h ∈ Ioi (0 : ℝ), 0 ≤ deriv m h)
  (hcont0 : ContinuousWithinAt m (Ici (0 : ℝ)) 0)
  (hmnn : ∀ h, 0 ≤ m h)
  (hm0 : m 0 = 0)
  (heq12 : ∀ h ∈ Ioi (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h)) :
-- imply
  ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (K / 4), c * Real.sqrt h ≤ m h := by
-- proof
  apply StatMech.Sharpness.ab_field_meanfield_bound_pos K hK m hdiff hmono hcont0 hmnn hm0 heq12

/--
[ab_perco_meanfield_sqrt_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean)
-/
@[path]
private lemma ab_perco_meanfield_sqrt_physical_eq
  {M : ℝ → ℝ → ℝ}
  {J βc : ℝ}
-- given
  (hβc : 0 < βc)
  (hJ : 0 < J)
  (hAB : AizenmanBarskyInequalityPhysical M J)
  (hdiff : ∀ h ∈ Ioi (0 : ℝ), DifferentiableAt ℝ (fun t => M βc t) h)
  (hmono : ∀ h ∈ Ioi (0 : ℝ), 0 ≤ deriv (fun t => M βc t) h)
  (hcont0 : ContinuousWithinAt (fun t => M βc t) (Ici (0 : ℝ)) 0)
  (hmnn : ∀ h, 0 ≤ M βc h)
  (hm0 : M βc 0 = 0)
  (heq6 : ∀ h ∈ Ioi (0 : ℝ), 1 - M βc h ≤ βc * deriv (fun b => M b h) βc) :
-- imply
  ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (βc * J / 4), c * Real.sqrt h ≤ M βc h := by
-- proof
  apply StatMech.Sharpness.ab_perco_meanfield_sqrt_physical M J βc hβc hJ hAB hdiff hmono hcont0 hmnn hm0 heq6


-- created on 2026-10-23
