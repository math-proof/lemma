import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFull.Part2
open MeasureTheory Real Set Filter Topology StatMech StatMech.Sharpness


/--
[si4_phiIsing_ge_one_above_tildeBc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFull.lean)
-/
@[path]
private lemma si4_phiIsing_ge_one_above_tildeBc_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
-- given
  (hβ0 : 0 ≤ β)
  (hbdd : BddAbove (tildeBetaCIsingSet d))
  (hβ : tildeBetaCIsing d < β) :
-- imply
  ∀ S : Finset (Site d), origin d ∈ S → 1 ≤ phiIsing d β S := by
-- proof
  apply StatMech.Sharpness.si4_phiIsing_ge_one_above_tildeBc d β hβ0 hbdd hβ

/--
[si4_mfd_drop_infphi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFull.lean)
-/
@[path]
private lemma si4_mfd_drop_infphi_eq
  {d : ℕ}
  {β infφ cn un εn : ℝ}
-- given
  (hβ : 0 < β)
  (hcn : 0 ≤ cn)
  (hinf : 1 ≤ infφ)
  (hun : un ≤ 1) :
-- imply
  2 * cn * ((1 / β) * (1 - un) - εn) ≤ 2 * cn * ((1 / β) * (infφ * (1 - un)) - εn) := by
-- proof
  apply StatMech.Sharpness.si4_mfd_drop_infphi β infφ cn un εn hβ hcn hinf hun

/--
[si4_mfd_limit_passage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFull.lean)
-/
@[path]
private lemma si4_mfd_limit_passage_eq
  {d : ℕ}
  {β infφ : ℝ}
  {u u' : ℝ}
  {un un' cn εn : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hinf : 1 ≤ infφ)
  (hun : Tendsto un atTop (𝓝 u))
  (hun' : Tendsto un' atTop (𝓝 u'))
  (hcn : Tendsto cn atTop (𝓝 1))
  (hεn : Tendsto εn atTop (𝓝 0))
  (hcnn : ∀ n, 0 ≤ cn n)
  (hunle : ∀ n, un n ≤ 1)
  (hfin : ∀ n, 2 * cn n * ((1 / β) * (infφ * (1 - un n)) - εn n) ≤ un' n) :
-- imply
  (2 / β) * (1 - u) ≤ u' := by
-- proof
  apply StatMech.Sharpness.si4_mfd_limit_passage β infφ hβ hinf u u' un un' cn εn hun hun' hcn hεn hcnn hunle hfin

/--
[si4_meanfield_lower_bound_of_finiteVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFull.lean)
-/
@[path]
private lemma si4_meanfield_lower_bound_of_finiteVolume_eq
  {d : ℕ}
  {β₀ : ℝ}
  {m : ℝ → ℝ}
  {infφ : ℝ}
  {un un' cn εn : ℝ → ℕ → ℝ}
  {β : ℝ}
-- given
  (hβ₀ : 0 < β₀)
  (hinf : 1 ≤ infφ)
  (hdiff : ∀ β ∈ Ici β₀, DifferentiableAt ℝ (fun β => (m β) ^ 2) β)
  (hzero : m β₀ = 0)
  (hnonneg : ∀ β ∈ Ici β₀, 0 ≤ m β)
  (hu : ∀ β ∈ Ioi β₀, Tendsto (un β) atTop (𝓝 ((m β) ^ 2)))
  (hderiv : ∀ β ∈ Ioi β₀, Tendsto (un' β) atTop (𝓝 (deriv (fun β => (m β) ^ 2) β)))
  (hc : ∀ β ∈ Ioi β₀, Tendsto (cn β) atTop (𝓝 1))
  (hε : ∀ β ∈ Ioi β₀, Tendsto (εn β) atTop (𝓝 0))
  (hcnn : ∀ β ∈ Ioi β₀, ∀ n, 0 ≤ cn β n)
  (hunle : ∀ β ∈ Ioi β₀, ∀ n, un β n ≤ 1)
  (hfin : ∀ β ∈ Ioi β₀, ∀ n, 2 * cn β n * ((1 / β) * (infφ * (1 - un β n)) - εn β n) ≤ un' β n)
  (hβ : β₀ ≤ β) :
-- imply
  Real.sqrt (1 - (β₀ / β) ^ 2) ≤ m β := by
-- proof
  apply StatMech.Sharpness.si4_meanfield_lower_bound_of_finiteVolume β₀ hβ₀ m infφ hinf un un' cn εn hdiff hzero hnonneg hu hderiv hc hε hcnn hunle hfin hβ

/--
[meanfield_lower_bound_of_initial_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFull.lean)
-/
@[path]
private lemma meanfield_lower_bound_of_initial_nonneg_eq
  {d : ℕ}
  {β₀ : ℝ}
  {m : ℝ → ℝ}
  {β : ℝ}
-- given
  (hβ₀ : 0 < β₀)
  (hdiff : ∀ β ∈ Ici β₀, DifferentiableAt ℝ (fun β => (m β) ^ 2) β)
  (hineq : ∀ β ∈ Ioi β₀, (2 / β) * (1 - (m β) ^ 2) ≤ deriv (fun β => (m β) ^ 2) β)
  (hnonneg : ∀ β ∈ Ici β₀, 0 ≤ m β)
  (hβ : β₀ ≤ β) :
-- imply
  Real.sqrt (1 - (β₀ / β) ^ 2) ≤ m β := by
-- proof
  apply StatMech.Sharpness.meanfield_lower_bound_of_initial_nonneg β₀ hβ₀ m hdiff hineq hnonneg hβ

/--
[sct_infiniteField_meanfield_inequality_of_deriv_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFull.lean)
-/
@[path]
private lemma sct_infiniteField_meanfield_inequality_of_deriv_tendsto_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (beta h : ℝ)
  (hbdd : BddAbove (tildeBetaCIsingSet d))
  (habove : tildeBetaCIsing d < beta)
  (hh : 0 < h)
  (hderiv : Tendsto (fun n : ℕ => deriv (fun b => (sctOriginMag d b h (n + 1)) ^ 2) beta) atTop (nhds (deriv (fun b => (sctInfiniteFieldMag d b h) ^ 2) beta))) :
-- imply
  (2 / beta) * (1 - (sctInfiniteFieldMag d beta h) ^ 2) ≤ deriv (fun b => (sctInfiniteFieldMag d b h) ^ 2) beta := by
-- proof
  apply StatMech.Sharpness.sct_infiniteField_meanfield_inequality_of_deriv_tendsto d beta h hbdd habove hh hderiv


-- created on 2026-10-23
