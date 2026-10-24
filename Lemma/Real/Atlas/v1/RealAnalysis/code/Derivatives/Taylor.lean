import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.RealAnalysis.code.Derivatives.Taylor
open Finset BigOperators


/--
[taylor_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/Taylor.lean)
-/
@[path]
lemma taylor_theorem
  {f : ℝ → ℝ}
  {n : ℕ}
  {x₀ x : ℝ}
-- given
  (hx : x₀ < x)
  (hf : ContDiffOn ℝ (↑n) f (Set.Icc x₀ x))
  (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Set.Icc x₀ x)) (Set.Ioo x₀ x)) :
-- imply
  ∃ c ∈ Set.Ioo x₀ x, f x = (∑ k ∈ Finset.range (n + 1), iteratedDerivWithin k f (Set.Icc x₀ x) x₀ / k.factorial * (x - x₀) ^ k) + iteratedDerivWithin (n + 1) f (Set.Icc x₀ x) c / (n + 1).factorial * (x - x₀) ^ (n + 1) := by
-- proof
  obtain ⟨c, hc_mem, hc_eq⟩ := taylor_mean_remainder_lagrange hx hf hf'
  refine ⟨c, hc_mem, ?_⟩
  rw [taylor_within_apply] at hc_eq
  have hsum_eq : (∑ k ∈ Finset.range (n + 1),
    ((↑k.factorial)⁻¹ * (x - x₀) ^ k) • iteratedDerivWithin k f (Set.Icc x₀ x) x₀) =
    (∑ k ∈ Finset.range (n + 1),
      iteratedDerivWithin k f (Set.Icc x₀ x) x₀ / ↑k.factorial * (x - x₀) ^ k) := by
    congr 1; ext k; simp [smul_eq_mul, div_eq_inv_mul]; ring
  linarith [show iteratedDerivWithin (n + 1) f (Set.Icc x₀ x) c * (x - x₀) ^ (n + 1) /
    ↑(n + 1).factorial = iteratedDerivWithin (n + 1) f (Set.Icc x₀ x) c /
    ↑(n + 1).factorial * (x - x₀) ^ (n + 1) from by ring]

/--
[second_derivative_test_min](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/Taylor.lean)
-/
@[path]
lemma second_derivative_test_min
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (hf : ContDiffAt ℝ 2 f x₀)
  (hf1 : deriv f x₀ = 0)
  (hf2 : 0 < iteratedDeriv 2 f x₀) :
-- imply
  IsStrictLocalMin f x₀ := by
-- proof
  have h2 : deriv (deriv f) x₀ > 0 := by
    simp only [iteratedDeriv_succ] at hf2; exact hf2
  have hsign : ∀ᶠ x in nhds x₀, SignType.sign (deriv f x) = SignType.sign (x - x₀) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos h2 hf1
  rw [Metric.eventually_nhds_iff] at hsign
  obtain ⟨ε₁, hε₁_pos, hε₁⟩ := hsign
  have h1 : ContDiffAt ℝ 1 f x₀ := hf.of_le (by norm_num)
  rw [contDiffAt_one_iff] at h1
  obtain ⟨f', u, hu_nhds, _, hfderiv⟩ := h1
  rw [Metric.mem_nhds_iff] at hu_nhds
  obtain ⟨ε₂, hε₂_pos, hball_u⟩ := hu_nhds
  set r := min ε₁ ε₂
  have hr_pos : 0 < r := lt_min hε₁_pos hε₂_pos
  have hdiff_ball : ∀ z, dist z x₀ < r → DifferentiableAt ℝ f z := by
    intro z hz
    exact (hfderiv z (hball_u (Metric.mem_ball.mpr
      (lt_of_lt_of_le hz (min_le_right _ _))))).differentiableAt
  have hsign_ball : ∀ z, dist z x₀ < r →
    SignType.sign (deriv f z) = SignType.sign (z - x₀) := by
    intro z hz; exact hε₁ (lt_of_lt_of_le hz (min_le_left _ _))
  have hdist_between_left : ∀ y z, y < x₀ → dist y x₀ < r →
    z ∈ Set.Icc y x₀ → dist z x₀ < r := by
    intro y z hlt hy hz
    rw [Real.dist_eq] at hy ⊢
    rw [abs_of_nonpos (by linarith : y - x₀ ≤ 0)] at hy
    rw [abs_of_nonpos (by linarith [hz.2] : z - x₀ ≤ 0)]
    linarith [hz.1]
  have hdist_between_right : ∀ y z, x₀ < y → dist y x₀ < r →
    z ∈ Set.Icc x₀ y → dist z x₀ < r := by
    intro y z hgt hy hz
    rw [Real.dist_eq] at hy ⊢
    rw [abs_of_nonneg (by linarith : 0 ≤ y - x₀)] at hy
    rw [abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - x₀)]
    linarith [hz.2]
  show ∀ᶠ x in nhdsWithin x₀ {x₀}ᶜ, f x₀ < f x
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨r, hr_pos, fun {y} hy hyne => ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hyne
  obtain hlt | hgt := lt_or_gt_of_ne hyne
  ·
    have hcont : ContinuousOn f (Set.Icc y x₀) := fun z hz =>
      (hdiff_ball z (hdist_between_left y z hlt hy hz)).continuousAt.continuousWithinAt
    have hanti : StrictAntiOn f (Set.Icc y x₀) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc y x₀) hcont
      intro z hz
      rw [interior_Icc] at hz
      have hz_r := hdist_between_left y z hlt hy (Set.Ioo_subset_Icc_self hz)
      have hsz := hsign_ball z hz_r
      rw [sign_neg (by linarith [hz.2] : z - x₀ < 0)] at hsz
      exact sign_eq_neg_one_iff.mp hsz
    exact hanti (Set.left_mem_Icc.mpr hlt.le) (Set.right_mem_Icc.mpr hlt.le) hlt
  ·
    have hcont : ContinuousOn f (Set.Icc x₀ y) := fun z hz =>
      (hdiff_ball z (hdist_between_right y z hgt hy hz)).continuousAt.continuousWithinAt
    have hmono : StrictMonoOn f (Set.Icc x₀ y) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc x₀ y) hcont
      intro z hz
      rw [interior_Icc] at hz
      have hz_r := hdist_between_right y z hgt hy (Set.Ioo_subset_Icc_self hz)
      have hsz := hsign_ball z hz_r
      rw [sign_pos (by linarith [hz.1] : 0 < z - x₀)] at hsz
      exact sign_eq_one_iff.mp hsz
    exact hmono (Set.left_mem_Icc.mpr hgt.le) (Set.right_mem_Icc.mpr hgt.le) hgt


-- created on 2026-10-23
