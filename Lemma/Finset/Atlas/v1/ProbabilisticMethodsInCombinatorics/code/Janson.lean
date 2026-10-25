import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Janson.Part3
open Filter Real Janson JansonInequalities
open scoped Topology
open Filter Asymptotics Real
open Real


namespace Janson

/--
[triangle_free_delta_over_mu_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean)
-/
@[path]
lemma triangle_free_delta_over_mu_tendsto
  {p : ℕ → ℝ}
-- given
  (hp_pos : ∀ᶠ n in atTop, 0 < p n)
  (hp_small : Tendsto (fun n => p n * Real.sqrt n) atTop (𝓝 0)) :
-- imply
  Tendsto (fun (n : ℕ) => delta_triangles n (p n) / mu_triangles n (p n)) atTop (𝓝 0) := by
-- proof
  have hp2n : Tendsto (fun (n : ℕ) => (n : ℝ) * (p n) ^ 2) atTop (𝓝 0) := by
    have h := hp_small.pow 2
    simp only [zero_pow (by norm_num : 2 ≠ 0)] at h
    refine h.congr' ?_
    filter_upwards with n
    simp only [mul_pow, sq_sqrt (Nat.cast_nonneg' n)]
    ring
  have h3np2 : Tendsto (fun (n : ℕ) => 3 * ((n : ℝ) * (p n) ^ 2)) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = 3 * 0 from by ring]
    exact hp2n.const_mul 3
  apply squeeze_zero_norm' _ h3np2
  filter_upwards [hp_pos, Filter.eventually_ge_atTop 4] with n hn hn4
  simp only [delta_triangles, mu_triangles]
  have hp_nn : (0 : ℝ) < p n := hn
  have hn_cast : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hcn3_pos : (0 : ℝ) < (n.choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hmu_pos : (0 : ℝ) < (n.choose 3 : ℝ) * p n ^ 3 :=
    mul_pos hcn3_pos (pow_pos hp_nn 3)
  have h_ratio_nonneg : 0 ≤ (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * p n ^ 5 /
    ((n.choose 3 : ℝ) * p n ^ 3) := by
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact_mod_cast Nat.zero_le _
          · linarith
        · linarith
      · exact pow_nonneg (le_of_lt hp_nn) 5
    · exact le_of_lt hmu_pos
  rw [Real.norm_of_nonneg h_ratio_nonneg]
  rw [show p n ^ 5 = p n ^ 2 * p n ^ 3 from by ring]
  rw [show (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * (p n ^ 2 * p n ^ 3) /
    ((n.choose 3 : ℝ) * p n ^ 3) =
    (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) / (n.choose 3 : ℝ) * p n ^ 2 from by
    field_simp]
  have h_nat_bound : n.choose 2 * (n - 2) * (n - 3) ≤ 3 * n * n.choose 3 := by
    have h_c3_rel : n.choose 2 * (n - 2) = 3 * n.choose 3 := by
      have h := Nat.choose_succ_right_eq n 2
      simp only [show 2 + 1 = 3 from rfl] at h
      rw [Nat.choose_two_right] at h ⊢; omega
    nlinarith [Nat.sub_le n 3, h_c3_rel]
  have h_real_bound : (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) ≤
    3 * (n : ℝ) * (n.choose 3 : ℝ) := by
    have h_lhs_eq : (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) =
      ((n.choose 2 * (n - 2) * (n - 3) : ℕ) : ℝ) := by
      push_cast
      simp [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n)]
    have h_rhs_eq : 3 * (n : ℝ) * (n.choose 3 : ℝ) =
      ((3 * n * n.choose 3 : ℕ) : ℝ) := by
      push_cast; ring
    rw [h_lhs_eq, h_rhs_eq]; exact_mod_cast h_nat_bound
  calc (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) / (n.choose 3 : ℝ) * p n ^ 2
    ≤ 3 * (n : ℝ) * p n ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hcn3_pos]
      nlinarith [sq_nonneg (p n), h_real_bound]
    _ = 3 * ((n : ℝ) * p n ^ 2) := by ring

end Janson

namespace Janson

/--
[choose_three_cast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean)
-/
@[path]
lemma choose_three_cast
  {n : ℕ}
-- given
  (hn : 3 ≤ n) :
-- imply
  (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
-- proof
  have h_desc : n.descFactorial 3 = n * (n - 1) * (n - 2) := by
    simp [Nat.descFactorial]; ring
  rw [Nat.choose_eq_descFactorial_div_factorial, h_desc]
  have h_div6 : 6 ∣ n * (n - 1) * (n - 2) := by
    rw [← h_desc, show (6 : ℕ) = (3 : ℕ).factorial from by norm_num]
    exact Nat.factorial_dvd_descFactorial n 3
  rw [show (3 : ℕ).factorial = 6 from by norm_num]
  have h_cast : (↑(n * (n - 1) * (n - 2)) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  rw [Nat.cast_div h_div6 (by norm_num : (6 : ℝ) ≠ 0), h_cast]
  norm_num

end Janson

namespace Janson

/--
[const_div_n_mul_sqrt_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean)
-/
@[path]
lemma const_div_n_mul_sqrt_tendsto
  {c : ℝ} :
-- imply
  Tendsto (fun n : ℕ => c / (n : ℝ) * Real.sqrt n) atTop (𝓝 0) := by
-- proof
  have heq : ∀ᶠ n : ℕ in atTop, c / (n : ℝ) * Real.sqrt n = c / Real.sqrt n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    rw [div_mul_eq_mul_div, show c * Real.sqrt n / (n : ℝ) = c * (Real.sqrt n / n) from by ring]
    congr 1
    field_simp
    exact Real.sq_sqrt (le_of_lt hn_pos)
  have hlim : Tendsto (fun n : ℕ => c / Real.sqrt n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  exact hlim.congr' (heq.mono fun n h => h.symm)

end Janson

namespace Janson

/--
[mu_triangles_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean)
-/
@[path]
lemma mu_triangles_tendsto
  {c : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (fun n : ℕ => mu_triangles n (c / (n : ℝ))) atTop (𝓝 (c ^ 3 / 6)) := by
-- proof
  have key : ∀ᶠ n : ℕ in atTop, mu_triangles n (c / (n : ℝ)) =
    c ^ 3 / 6 * (1 - 1 / (n : ℝ)) * (1 - 2 / (n : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    simp only [mu_triangles]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    rw [choose_three_cast n (by omega : 3 ≤ n)]
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    field_simp
  have hlim : Tendsto (fun n : ℕ => c ^ 3 / 6 * (1 - 1 / (n : ℝ)) * (1 - 2 / (n : ℝ)))
    atTop (𝓝 (c ^ 3 / 6)) := by
    have h_inv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h_factor1 : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h_inv
    have h_factor2 : Tendsto (fun n : ℕ => 1 - 2 / (n : ℝ)) atTop (𝓝 1) := by
      have h2inv : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
        have := h_inv.const_mul 2
        simp only [mul_one_div, mul_zero] at this
        exact this
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h2inv
    conv_rhs => rw [show c ^ 3 / 6 = c ^ 3 / 6 * 1 * 1 from by ring]
    exact ((tendsto_const_nhds.mul h_factor1).mul h_factor2)
  exact hlim.congr' (key.mono fun n h => h.symm)

end Janson

namespace Janson

/--
[cor_triangle_free_delta_over_mu](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean)
-/
@[path]
lemma cor_triangle_free_delta_over_mu
  {c : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (fun n : ℕ => delta_triangles n (c / (n : ℝ)) / mu_triangles n (c / (n : ℝ))) atTop (𝓝 0) := by
-- proof
  apply triangle_free_delta_over_mu_tendsto
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact div_pos hc (by exact_mod_cast (show 0 < n by omega))
  · exact const_div_n_mul_sqrt_tendsto c

end Janson

namespace Janson

/--
[delta_triangles_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean)
-/
@[path]
lemma delta_triangles_tendsto_zero
  {c : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (fun n : ℕ => delta_triangles n (c / (n : ℝ))) atTop (𝓝 0) := by
-- proof
  have hmu := mu_triangles_tendsto c hc
  have h_ratio := cor_triangle_free_delta_over_mu c hc
  have hmu_pos : ∀ᶠ n : ℕ in atTop, 0 < mu_triangles n (c / (n : ℝ)) := by
    have : (0 : ℝ) < c ^ 3 / 6 := by positivity
    exact hmu.eventually (eventually_gt_nhds this)
  have heq : ∀ᶠ n : ℕ in atTop, delta_triangles n (c / (n : ℝ)) =
    (delta_triangles n (c / (n : ℝ)) / mu_triangles n (c / (n : ℝ))) *
      mu_triangles n (c / (n : ℝ)) := by
    filter_upwards [hmu_pos] with n hn
    rw [div_mul_cancel₀]; exact ne_of_gt hn
  rw [show (0 : ℝ) = 0 * (c ^ 3 / 6) from by ring]
  exact (h_ratio.mul hmu).congr' (heq.mono fun n h => h.symm)

end Janson

namespace Janson

/--
[corollary_8_1_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean)
-/
@[path]
lemma corollary_8_1_7
  {c : ℝ}
  {prob_tf : ℕ → ℝ}
-- given
  (hc : 0 < c)
  (hprob_pos : ∀ᶠ n in atTop, 0 < prob_tf n)
  (_hprob_le : ∀ᶠ n in atTop, prob_tf n ≤ 1)
  (h_upper : ∀ᶠ n in atTop, prob_tf n ≤ Real.exp (-(mu_triangles n (c / n)) + delta_triangles n (c / n) / 2))
  (h_lower : ∀ᶠ n in atTop, Real.exp (-(mu_triangles n (c / n))) ≤ prob_tf n) :
-- imply
  Tendsto (fun n : ℕ => -Real.log (prob_tf n)) atTop (𝓝 (c ^ 3 / 6)) := by
-- proof
  have h_squeeze_lower : ∀ᶠ n in atTop,
    mu_triangles n (c / n) - delta_triangles n (c / n) / 2 ≤ -Real.log (prob_tf n) := by
    filter_upwards [h_upper, hprob_pos] with n hu hp
    have h1 : Real.log (prob_tf n) ≤
      -(mu_triangles n (c / n)) + delta_triangles n (c / n) / 2 := by
      calc Real.log (prob_tf n)
        ≤ Real.log (Real.exp (-(mu_triangles n (c / n)) + delta_triangles n (c / n) / 2)) :=
          Real.log_le_log hp hu
        _ = -(mu_triangles n (c / n)) + delta_triangles n (c / n) / 2 := Real.log_exp _
    linarith
  have h_squeeze_upper : ∀ᶠ n in atTop,
    -Real.log (prob_tf n) ≤ mu_triangles n (c / n) := by
    filter_upwards [h_lower, hprob_pos] with n hl _hp
    have h1 : -(mu_triangles n (c / n)) ≤ Real.log (prob_tf n) := by
      calc -(mu_triangles n (c / n))
        = Real.log (Real.exp (-(mu_triangles n (c / n)))) := (Real.log_exp _).symm
        _ ≤ Real.log (prob_tf n) := Real.log_le_log (Real.exp_pos _) hl
    linarith
  have h_lower_lim : Tendsto (fun n : ℕ =>
    mu_triangles n (c / n) - delta_triangles n (c / n) / 2) atTop (𝓝 (c ^ 3 / 6)) := by
    have h_half_delta : Tendsto (fun n : ℕ => delta_triangles n (c / (n : ℝ)) / 2)
      atTop (𝓝 0) := by
      rw [show (0 : ℝ) = 0 / 2 from by ring]
      exact (delta_triangles_tendsto_zero c hc).div_const 2
    conv_rhs => rw [show c ^ 3 / 6 = c ^ 3 / 6 - 0 from by ring]
    exact (mu_triangles_tendsto c hc).sub h_half_delta
  have h_upper_lim : Tendsto (fun n : ℕ => mu_triangles n (c / (n : ℝ)))
    atTop (𝓝 (c ^ 3 / 6)) := mu_triangles_tendsto c hc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_lim h_upper_lim
    h_squeeze_lower h_squeeze_upper

end Janson

namespace JansonInequalities

/--
[janson_inequality_II](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean)
-/
@[path]
lemma janson_inequality_II
  {μ Δ v : ℝ}
-- given
  (hμ_pos : 0 < μ)
  (hΔ_ge_μ : Δ ≥ μ)
  (hbound : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → v ≤ Real.exp (-q * μ + q ^ 2 * Δ / 2)) :
-- imply
  v ≤ Real.exp (-(μ ^ 2) / (2 * Δ)) := by
-- proof
  have hΔ_pos : (0 : ℝ) < Δ := lt_of_lt_of_le hμ_pos hΔ_ge_μ
  have hq_nonneg : (0 : ℝ) ≤ μ / Δ := div_nonneg (le_of_lt hμ_pos) (le_of_lt hΔ_pos)
  have hq_le_one : μ / Δ ≤ 1 := div_le_one_of_le₀ hΔ_ge_μ (le_of_lt hΔ_pos)
  have key := hbound (μ / Δ) hq_nonneg hq_le_one
  suffices h : -(μ / Δ) * μ + (μ / Δ) ^ 2 * Δ / 2 = -(μ ^ 2) / (2 * Δ) by
    rwa [h] at key
  field_simp
  ring

end JansonInequalities

namespace JansonInequalities

/--
[mu_sq_over_delta_isTheta](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean)
-/
@[path]
lemma mu_sq_over_delta_isTheta
  {μ Δ p : ℕ → ℝ}
-- given
  (hμ_theta : μ =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 3 * p n ^ 3))
  (hΔ_theta : Δ =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 4 * p n ^ 5))
  (hp_pos : ∀ᶠ (n : ℕ) in atTop, 0 < p n)
  (hn_pos : ∀ᶠ (n : ℕ) in atTop, (0 : ℝ) < n)
  (hΔ_pos : ∀ᶠ (n : ℕ) in atTop, 0 < Δ n) :
-- imply
  (fun n : ℕ => μ n ^ 2 / (2 * Δ n)) =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 2 * p n) := by
-- proof
  have hμ_sq : (fun n : ℕ => μ n ^ 2) =Θ[atTop]
    (fun n : ℕ => ((n : ℝ) ^ 3 * p n ^ 3) ^ 2) := hμ_theta.pow 2
  have hμ_sq_div_Δ : (fun n : ℕ => μ n ^ 2 / Δ n) =Θ[atTop]
    (fun n : ℕ => ((n : ℝ) ^ 3 * p n ^ 3) ^ 2 / ((n : ℝ) ^ 4 * p n ^ 5)) :=
    hμ_sq.div hΔ_theta
  have h_simp : (fun n : ℕ => ((n : ℝ) ^ 3 * p n ^ 3) ^ 2 / ((n : ℝ) ^ 4 * p n ^ 5))
    =ᶠ[atTop] (fun n : ℕ => (n : ℝ) ^ 2 * p n) := by
    filter_upwards [hp_pos, hn_pos] with n hp hn
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn
    have hp_ne : p n ≠ 0 := ne_of_gt hp
    field_simp
  have h4 : (fun n : ℕ => μ n ^ 2 / Δ n) =Θ[atTop]
    (fun n : ℕ => (n : ℝ) ^ 2 * p n) :=
    hμ_sq_div_Δ.trans h_simp.isTheta
  have h5 : (fun n : ℕ => μ n ^ 2 / (2 * Δ n)) =ᶠ[atTop]
    (fun n : ℕ => (1 / 2 : ℝ) * (μ n ^ 2 / Δ n)) := by
    filter_upwards [hΔ_pos] with n hΔ
    have hΔ_ne : Δ n ≠ 0 := ne_of_gt hΔ
    field_simp
  have h6 : (fun n : ℕ => (1 / 2 : ℝ) * (μ n ^ 2 / Δ n)) =Θ[atTop]
    (fun n : ℕ => (n : ℝ) ^ 2 * p n) := by
    rwa [Asymptotics.isTheta_const_mul_left (show (1 / 2 : ℝ) ≠ 0 from by norm_num)]
  exact h5.isTheta.trans h6

end JansonInequalities

/--
[isTheta_natCast_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean)
-/
@[path]
private lemma isTheta_natCast_sub_const_eq
  {k : ℕ} :
-- imply
  (fun n : ℕ => (n : ℝ) - (k : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
-- proof
  apply JansonInequalities.isTheta_natCast_sub_const k


-- created on 2026-10-23
