import Mathlib
import sympy.Basic

open MeasureTheory Set

/--
[AddSubgroup_exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddSubgroup_exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology.lean)
-/

private lemma  integrable_inv_one_add_abs_sq :
  Integrable (fun t : ℝ => (1 + |t|)⁻¹ ^ 2) := by
  have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
    (by rw [Module.finrank_self]; norm_num))
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  have ht : 0 < 1 + |t| := by positivity
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg ht.le, Real.rpow_two, inv_pow]

private lemma  integrable_prod_inv_one_add_abs_sq (r : ℕ) :
  Integrable (fun z : Fin r → ℝ => ∏ k, (1 + |z k|)⁻¹ ^ 2) := by
  have h := Integrable.fintype_prod (ι := Fin r) (𝕜 := ℝ) (μ := fun _ => (volume : Measure ℝ))
    (f := fun _ t => (1 + |t|)⁻¹ ^ 2) (fun _ => integrable_inv_one_add_abs_sq)
  rwa [← volume_pi] at h

private lemma  prod_inv_one_add_abs_sq_nonneg {r : ℕ} (z : Fin r → ℝ) :
  0 ≤ ∏ k, (1 + |z k|)⁻¹ ^ 2 :=
  Finset.prod_nonneg fun k _ => by positivity

private lemma  prod_le_pow_mul_prod_of_dist_lt {r : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (a z : Fin r → ℝ) (hz : dist z a < ρ) :
  ∏ k, (1 + |a k|)⁻¹ ^ 2 ≤ (1 + ρ) ^ (2 * r) * ∏ k, (1 + |z k|)⁻¹ ^ 2 := by
  have hk : ∀ k, (1 + |a k|)⁻¹ ^ 2 ≤ (1 + ρ) ^ 2 * (1 + |z k|)⁻¹ ^ 2 := by
    intro k
    have hd : |z k - a k| ≤ ρ := by
      have := dist_le_pi_dist z a k
      rw [Real.dist_eq] at this
      linarith
    have ha : 0 < 1 + |a k| := by positivity
    have hzk : 0 < 1 + |z k| := by positivity
    have h1 : 1 + |z k| ≤ (1 + ρ) * (1 + |a k|) := by
      have : |z k| ≤ |a k| + ρ := calc
        _ = |a k + (z k - a k)| := by ring_nf
        _ ≤ |a k| + |z k - a k| := abs_add_le _ _
        _ ≤ |a k| + ρ := by linarith
      nlinarith [abs_nonneg (a k)]
    have h2 : (1 + |a k|)⁻¹ ≤ (1 + ρ) * (1 + |z k|)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ ha]
      calc _ = (1 + |z k|) * (1 + |z k|)⁻¹ := by field_simp
        _ ≤ (1 + ρ) * (1 + |a k|) * (1 + |z k|)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hzk.le)
        _ = (1 + ρ) * (1 + |z k|)⁻¹ * (1 + |a k|) := by ring
    calc _ ≤ ((1 + ρ) * (1 + |z k|)⁻¹) ^ 2 :=
          pow_le_pow_left₀ (inv_nonneg.2 ha.le) h2 2
      _ = (1 + ρ) ^ 2 * (1 + |z k|)⁻¹ ^ 2 := by ring
  calc _ ≤ ∏ k, ((1 + ρ) ^ 2 * (1 + |z k|)⁻¹ ^ 2) :=
        Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => hk k
    _ = (1 + ρ) ^ (2 * r) * ∏ k, (1 + |z k|)⁻¹ ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

private lemma  mul_prod_le_pow_mul_setIntegral {r : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (a : Fin r → ℝ) :
  (2 * ρ) ^ r * ∏ k, (1 + |a k|)⁻¹ ^ 2 ≤
      (1 + ρ) ^ (2 * r) * ∫ z in Metric.ball a ρ, ∏ k, (1 + |z k|)⁻¹ ^ 2 := by
  have hvol : (volume (Metric.ball a ρ)).toReal = (2 * ρ) ^ r := by
    rw [Real.volume_pi_ball a hρ, Fintype.card_fin, ENNReal.toReal_ofReal (by positivity)]
  have hfin : volume (Metric.ball a ρ) < ⊤ := by
    rw [Real.volume_pi_ball a hρ]; exact ENNReal.ofReal_lt_top
  have hpos : 0 < (1 + ρ) ^ (2 * r) := by positivity

  have hconst : ∫ _ in Metric.ball a ρ, ((1 + ρ) ^ (2 * r))⁻¹ * ∏ k, (1 + |a k|)⁻¹ ^ 2 =
      (2 * ρ) ^ r * (((1 + ρ) ^ (2 * r))⁻¹ * ∏ k, (1 + |a k|)⁻¹ ^ 2) := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, hvol]
  have hmono : ∫ _ in Metric.ball a ρ, ((1 + ρ) ^ (2 * r))⁻¹ * ∏ k, (1 + |a k|)⁻¹ ^ 2 ≤
      ∫ z in Metric.ball a ρ, ∏ k, (1 + |z k|)⁻¹ ^ 2 := by
    refine setIntegral_mono_on (integrableOn_const hfin.ne)
      (integrable_prod_inv_one_add_abs_sq r).integrableOn measurableSet_ball fun z hz => ?_
    rw [inv_mul_le_iff₀ hpos]
    exact prod_le_pow_mul_prod_of_dist_lt hρ.le a z (Metric.mem_ball.1 hz)
  rw [hconst] at hmono
  calc _ = (1 + ρ) ^ (2 * r) *
      ((2 * ρ) ^ r * (((1 + ρ) ^ (2 * r))⁻¹ * ∏ k, (1 + |a k|)⁻¹ ^ 2)) := by
        field_simp
    _ ≤ (1 + ρ) ^ (2 * r) * ∫ z in Metric.ball a ρ, ∏ k, (1 + |z k|)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left hmono hpos.le

private lemma  exists_pos_forall_norm_le {r : ℕ} {Γ : AddSubgroup (Fin r → ℝ)} [DiscreteTopology Γ] :
  ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Γ, x ≠ 0 → δ ≤ ‖x‖ := by
  have hopen : IsOpen ({0} : Set Γ) := isOpen_discrete _
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen 0 rfl
  refine ⟨δ, hδ, fun x hx hx0 => ?_⟩
  by_contra h
  have h : ‖x‖ < δ := lt_of_not_ge h
  have hmem : (⟨x, hx⟩ : Γ) ∈ Metric.ball (0 : Γ) δ := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    simpa using h
  have := hball hmem
  rw [Set.mem_singleton_iff, Subtype.ext_iff] at this
  exact hx0 this

private lemma  exists_forall_sum_le {r : ℕ} {Γ : AddSubgroup (Fin r → ℝ)} [DiscreteTopology Γ] :
  ∃ K : ℝ, ∀ (y : Fin r → ℝ) (F : Finset (Fin r → ℝ)), (↑F : Set (Fin r → ℝ)) ⊆ Γ →
      ∑ x ∈ F, ∏ k, (1 + |y k + x k|)⁻¹ ^ 2 ≤ K := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_forall_norm_le (Γ := Γ)
  set ρ : ℝ := δ / 2 with hρ_def
  have hρ : 0 < ρ := by positivity
  set I : ℝ := ∫ z : Fin r → ℝ, ∏ k, (1 + |z k|)⁻¹ ^ 2 with hI_def
  refine ⟨((2 * ρ) ^ r)⁻¹ * ((1 + ρ) ^ (2 * r) * I), fun y F hF => ?_⟩
  have h2ρ : 0 < (2 * ρ) ^ r := by positivity

  have hdisj : Set.Pairwise (↑F : Set (Fin r → ℝ))
    (Function.onFun Disjoint fun x => Metric.ball (y + x) ρ) := by
    intro x hx x' hx' hne
    refine Metric.ball_disjoint_ball ?_
    have hmem : x - x' ∈ Γ := Γ.sub_mem (hF hx) (hF hx')
    have hne' : x - x' ≠ 0 := sub_ne_zero.2 hne
    have hle := hsep _ hmem hne'
    have hdist : dist (y + x) (y + x') = ‖x - x'‖ := by
      rw [dist_eq_norm]; congr 1; abel
    rw [hdist, hρ_def]; linarith

  have hsum : (2 * ρ) ^ r * ∑ x ∈ F, ∏ k, (1 + |y k + x k|)⁻¹ ^ 2 ≤
      (1 + ρ) ^ (2 * r) * ∑ x ∈ F, ∫ z in Metric.ball (y + x) ρ, ∏ k, (1 + |z k|)⁻¹ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have := mul_prod_le_pow_mul_setIntegral hρ (y + x)
    simpa only [Pi.add_apply] using this
  have hunion : ∑ x ∈ F, ∫ z in Metric.ball (y + x) ρ, ∏ k, (1 + |z k|)⁻¹ ^ 2 =
      ∫ z in ⋃ x ∈ F, Metric.ball (y + x) ρ, ∏ k, (1 + |z k|)⁻¹ ^ 2 :=
    (integral_biUnion_finset F (fun _ _ => measurableSet_ball) hdisj
      (fun _ _ => (integrable_prod_inv_one_add_abs_sq r).integrableOn)).symm
  have hle : ∫ z in ⋃ x ∈ F, Metric.ball (y + x) ρ, ∏ k, (1 + |z k|)⁻¹ ^ 2 ≤ I :=
    setIntegral_le_integral (integrable_prod_inv_one_add_abs_sq r)
      (Filter.Eventually.of_forall fun z => prod_inv_one_add_abs_sq_nonneg z)
  rw [hunion] at hsum
  have hpow : 0 ≤ (1 + ρ) ^ (2 * r) := by positivity
  have h3 : (2 * ρ) ^ r * ∑ x ∈ F, ∏ k, (1 + |y k + x k|)⁻¹ ^ 2 ≤ (1 + ρ) ^ (2 * r) * I :=
    hsum.trans (mul_le_mul_of_nonneg_left hle hpow)
  rwa [le_inv_mul_iff₀ h2ρ]
@[path]
private lemma main
  {r : ℕ}
  {Γ : AddSubgroup (Fin r → ℝ)} [DiscreteTopology Γ] :
-- imply
  ∃ K : ℝ, ∀ (y : Fin r → ℝ) (F : Finset (Fin r → ℝ)), (↑F : Set (Fin r → ℝ)) ⊆ Γ →
      ∑ x ∈ F, ∏ k, (1 + |y k + x k|)⁻¹ ^ 2 ≤ K :=
-- proof
  exists_forall_sum_le (Γ := Γ)


-- created on 2026-10-09
