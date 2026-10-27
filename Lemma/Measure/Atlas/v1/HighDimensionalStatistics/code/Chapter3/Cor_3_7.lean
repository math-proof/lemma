import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Cor_3_7
open Matrix MeasureTheory Rigollet Rigollet.Chapter3


namespace Rigollet.Chapter3

/--
[le_add_min_of_le_both](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma le_add_min_of_le_both
  {x a t₁ t₂ c : ℝ}
-- given
  (h₁ : x ≤ a + t₁ + c)
  (h₂ : x ≤ a + t₂ + c) :
-- imply
  x ≤ a + min t₁ t₂ + c := by
-- proof
  obtain h | h := le_total t₁ t₂
  · rw [min_eq_left h]; exact h₁
  · rw [min_eq_right h]; exact h₂

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[MSE_37_eq_Chapter3_MSE](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma MSE_37_eq_Chapter3_MSE
  {n : ℕ}
  {fhat f : Fin n → ℝ} :
-- imply
  MSE_37 fhat f = Chapter3.MSE fhat f := by
-- proof
  simp [MSE_37, Chapter3.MSE]

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[support_size_37_eq_Chapter3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma support_size_37_eq_Chapter3
  {M : ℕ}
  {θ : Fin M → ℝ} :
-- imply
  support_size_37 θ = Chapter3.support_size θ := by
-- proof
  simp [support_size_37, Chapter3.support_size]

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[l1norm_37_eq_Chapter3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma l1norm_37_eq_Chapter3
  {M : ℕ}
  {θ : Fin M → ℝ} :
-- imply
  l1norm_37 θ = Chapter3.l1norm θ := by
-- proof
  simp [l1norm_37, Chapter3.l1norm]

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[maurey_approximation_37](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma maurey_approximation_37
  {n M : ℕ}
  {Φ : Matrix (Fin n) (Fin M) ℝ}
  {f : Fin n → ℝ}
  {θ' : Fin M → ℝ}
  {k : ℕ}
-- given
  (hn : 0 < n)
  (hM : 0 < M)
  (hNorm : DictNormalized Φ)
  (hk : 1 ≤ k) :
-- imply
  ∃ θ : Fin M → ℝ, support_size_37 θ ≤ 2 * k ∧ MSE_37 (Φ.mulVec θ) f ≤ MSE_37 (Φ.mulVec θ') f + (l1norm_37 θ') ^ 2 / (k : ℝ) := by
-- proof
  by_cases hR : l1norm_37 θ' = 0
  · refine ⟨θ', ?_, ?_⟩
    · have h0 : ∀ i, θ' i = 0 := by
      intro i
      have : |θ' i| = 0 := by
        have hnn : 0 ≤ |θ' i| := abs_nonneg _
        have hsum : |θ' i| ≤ l1norm_37 θ' :=
          Finset.single_le_sum (fun j _ => abs_nonneg (θ' j)) (Finset.mem_univ i)
        linarith [hR]
      exact abs_eq_zero.mp this
      have : support_size_37 θ' = 0 := by unfold support_size_37; simp [h0]
      omega
    · have : (l1norm_37 θ') ^ 2 / (k : ℝ) = 0 := by simp [hR]
      linarith
  · have hR_pos : 0 < l1norm_37 θ' := by
    have hnn : 0 ≤ l1norm_37 θ' := Finset.sum_nonneg (fun i _ => abs_nonneg (θ' i))
    exact lt_of_le_of_ne hnn (Ne.symm hR)
    have hNorm1 : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ (1 : ℝ) ^ 2 * ↑n := by
      intro j; simp; exact hNorm j
    obtain ⟨θ, hθ_sparse, hθ_mse⟩ := Chapter3.maurey_sparse_approx hn hM Φ f
      (1 : ℝ) one_pos hNorm1 k hk (l1norm_37 θ') hR_pos θ'
      (by rw [l1norm_37_eq_Chapter3])
    refine ⟨θ, ?_, ?_⟩
    · rwa [support_size_37_eq_Chapter3]
    · rw [MSE_37_eq_Chapter3_MSE, MSE_37_eq_Chapter3_MSE]
      calc Chapter3.MSE (Φ *ᵥ θ) f
        ≤ Chapter3.MSE (Φ *ᵥ θ') f + 1 ^ 2 * l1norm_37 θ' ^ 2 / ↑k := hθ_mse
        _ = Chapter3.MSE (Φ *ᵥ θ') f + l1norm_37 θ' ^ 2 / ↑k := by ring

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[opt_bound_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma opt_bound_sqrt
  {a b k : ℝ}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hk_pos : 0 < k)
  (hk_le : k ≤ Real.sqrt (a / b))
  (hk_ge : Real.sqrt (a / b) / 2 ≤ k) :
-- imply
  a / k + b * k ≤ 3 * Real.sqrt (a * b) := by
-- proof
  set s := Real.sqrt (a / b)
  set t := Real.sqrt (a * b)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (div_pos ha hb)
  have ht_nn : 0 ≤ t := Real.sqrt_nonneg _
  have hsq1 : s ^ 2 = a / b := Real.sq_sqrt (le_of_lt (div_pos ha hb))
  have hsq2 : t ^ 2 = a * b := Real.sq_sqrt (by positivity : 0 ≤ a * b)
  have hsb : s ^ 2 * b = a := by field_simp at hsq1; linarith
  have hst : s * t = a := by
    have h1 : (s * t) ^ 2 = a ^ 2 := by nlinarith [hsb, hsq2]
    nlinarith [sq_nonneg (s * t - a), sq_nonneg (s * t + a),
      mul_nonneg (le_of_lt hs_pos) ht_nn]
  have hbs : b * s = t := by
    have h1 : (b * s) ^ 2 = t ^ 2 := by nlinarith [hsb, hsq2]
    nlinarith [sq_nonneg (b * s - t), sq_nonneg (b * s + t),
      mul_nonneg (le_of_lt hb) (le_of_lt hs_pos)]
  have h1 : a / k ≤ 2 * t := by
    rw [div_le_iff₀ hk_pos]; nlinarith [hst]
  have h2 : b * k ≤ t := by nlinarith [hbs]
  linarith

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[floor_ge_half_of_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma floor_ge_half_of_ge_one
  {x : ℝ}
-- given
  (hx : 1 ≤ x) :
-- imply
  x / 2 ≤ ↑(Nat.floor x) := by
-- proof
  have hf : x < ↑(Nat.floor x) + 1 := Nat.lt_floor_add_one x
  have hf2 : ↑(Nat.floor x) ≤ x := Nat.floor_le (by linarith : 0 ≤ x)
  by_cases hx2 : x < 2
  · have h1 : 1 ≤ Nat.floor x := by
    rwa [Nat.one_le_iff_ne_zero, ne_eq, Nat.floor_eq_zero, not_lt]
    have : (1 : ℝ) ≤ ↑(Nat.floor x) := by exact_mod_cast h1
    linarith
  · push Not at hx2; linarith

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[six_sqrt_le_of_ge_36](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma six_sqrt_le_of_ge_36
  {C : ℝ}
-- given
  (hC : 0 < C)
  (hC36 : 36 ≤ C) :
-- imply
  6 * Real.sqrt C ≤ C := by
-- proof
  have hsq : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC.le
  have hge6 : 6 ≤ Real.sqrt C := by
    by_contra h; push Not at h
    nlinarith [Real.sqrt_nonneg C]
  nlinarith [Real.sqrt_nonneg C]

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[sqrt_ratio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma sqrt_ratio_eq
  {R σ C L : ℝ}
-- given
  (hR : 0 < R)
  (hσ : 0 < σ)
  (hCL : 0 < C * L) :
-- imply
  Real.sqrt (R ^ 2 / (C * σ ^ 2 * L)) = R / (σ * Real.sqrt (C * L)) := by
-- proof
  have hd : 0 < σ * Real.sqrt (C * L) := mul_pos hσ (Real.sqrt_pos.mpr hCL)
  conv_lhs => rw [show C * σ ^ 2 * L = (σ * Real.sqrt (C * L)) ^ 2 from by
    rw [mul_pow, Real.sq_sqrt hCL.le]; ring]
  rw [show R ^ 2 / (σ * Real.sqrt (C * L)) ^ 2 = (R / (σ * Real.sqrt (C * L))) ^ 2 from
    (div_pow _ _ _).symm]
  exact Real.sqrt_sq (div_pos hR hd).le

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[maurey_opt_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma maurey_opt_algebra
  {R σ C L k : ℝ}
-- given
  (hR : 0 < R)
  (hσ : 0 < σ)
  (hC : 0 < C)
  (hL : 0 < L)
  (hk : 0 < k)
  (hk_le : k ≤ R / (σ * Real.sqrt (C * L)))
  (hk_ge : R / (σ * Real.sqrt (C * L)) / 2 ≤ k)
  (hC36 : 36 ≤ C) :
-- imply
  2 * R ^ 2 / k + 2 * (C * σ ^ 2 * L) * k ≤ C * σ * R * Real.sqrt L := by
-- proof
  have hCL : 0 < C * L := mul_pos hC hL
  rw [← sqrt_ratio_eq R σ C L hR hσ hCL] at hk_le hk_ge
  have h_bound := opt_bound_sqrt (R ^ 2) (C * σ ^ 2 * L) k (sq_pos_of_pos hR)
    (by positivity) hk hk_le hk_ge
  have h_sqrt : Real.sqrt (R ^ 2 * (C * σ ^ 2 * L)) = R * σ * Real.sqrt (C * L) := by
    rw [show R ^ 2 * (C * σ ^ 2 * L) = (R * σ) ^ 2 * (C * L) from by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ (R * σ) ^ 2)]
    rw [Real.sqrt_sq (by positivity : 0 ≤ R * σ)]
  rw [h_sqrt] at h_bound
  have h2 : 2 * R ^ 2 / k + 2 * (C * σ ^ 2 * L) * k ≤
    6 * (R * σ * Real.sqrt (C * L)) := by
    have eq1 : 2 * R ^ 2 / k = 2 * (R ^ 2 / k) := by ring
    have eq2 : 2 * (C * σ ^ 2 * L) * k = 2 * (C * σ ^ 2 * L * k) := by ring
    rw [eq1, eq2]; linarith
  rw [Real.sqrt_mul hC.le] at h2
  calc 2 * R ^ 2 / k + 2 * (C * σ ^ 2 * L) * k
    ≤ 6 * (R * σ * (Real.sqrt C * Real.sqrt L)) := h2
    _ = (6 * Real.sqrt C) * (σ * R * Real.sqrt L) := by ring
    _ ≤ C * (σ * R * Real.sqrt L) :=
      mul_le_mul_of_nonneg_right (six_sqrt_le_of_ge_36 C hC hC36) (by positivity)
    _ = C * σ * R * Real.sqrt L := by ring

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[maurey_three_case_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma maurey_three_case_bound
  {n M : ℕ}
  {Φ : Matrix (Fin n) (Fin M) ℝ}
  {f : Fin n → ℝ}
  {σ : ℝ}
  {C_const : ℝ}
  {fhat' : Fin n → ℝ}
  {θ' : Fin M → ℝ}
  {tail : ℝ}
-- given
  (_hn : 0 < n)
  (_hM : 0 < M)
  (_hNorm : DictNormalized Φ)
  (hσ : 0 < σ)
  (hC : 0 < C_const)
  (hMaurey : ∀ k : ℕ, 1 ≤ k → ∃ θ : Fin M → ℝ, support_size_37 θ ≤ 2 * k ∧ MSE_37 (Φ.mulVec θ) f ≤ MSE_37 (Φ.mulVec θ') f + (l1norm_37 θ') ^ 2 / (k : ℝ))
  (h_l0 : ∀ θ : Fin M → ℝ, MSE_37 fhat' f ≤ 2 * MSE_37 (Φ.mulVec θ) f + C_const * σ ^ 2 * ↑(support_size_37 θ) * Real.log (Real.exp 1 * ↑M) / ↑n + tail)
  (hC_large : 36 ≤ C_const)
  (hR_lower : σ * Real.sqrt (C_const * (Real.log (Real.exp 1 * ↑M) / ↑n)) ≤ l1norm_37 θ') :
-- imply
  MSE_37 fhat' f ≤ 2 * MSE_37 (Φ.mulVec θ') f + C_const * σ * l1norm_37 θ' * Real.sqrt (Real.log (Real.exp 1 * ↑M) / ↑n) + tail := by
-- proof
  set R := l1norm_37 θ' with hR_def
  set L := Real.log (Real.exp 1 * ↑M) / ↑n with hL_def
  have hL_pos : 0 < L := by
    apply div_pos
    · apply Real.log_pos
      calc (1 : ℝ) < Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
        _ = Real.exp 1 * 1 := (mul_one _).symm
        _ ≤ Real.exp 1 * ↑M := by
          apply mul_le_mul_of_nonneg_left
          · exact Nat.one_le_cast.mpr _hM
          · exact le_of_lt (Real.exp_pos 1)
    · exact Nat.cast_pos.mpr _hn
  have hCL_pos : 0 < C_const * L := mul_pos hC hL_pos
  have hR_pos : 0 < R := by
    calc (0 : ℝ) < σ * Real.sqrt (C_const * L) :=
      mul_pos hσ (Real.sqrt_pos.mpr hCL_pos)
      _ ≤ R := hR_lower
  have hd_pos : 0 < σ * Real.sqrt (C_const * L) :=
    mul_pos hσ (Real.sqrt_pos.mpr hCL_pos)
  set kbar := R / (σ * Real.sqrt (C_const * L))
  have hkbar_ge1 : 1 ≤ kbar := by rw [le_div_iff₀ hd_pos]; linarith
  set k := Nat.floor kbar with hk_def
  have hk_ge1 : 1 ≤ k := by
    rwa [Nat.one_le_iff_ne_zero, ne_eq, Nat.floor_eq_zero, not_lt]
  have hk_pos : (0 : ℝ) < (k : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk_ge1))
  have hk_le_kbar : (k : ℝ) ≤ kbar := Nat.floor_le (by linarith : 0 ≤ kbar)
  have hk_ge_half : kbar / 2 ≤ (k : ℝ) := floor_ge_half_of_ge_one kbar hkbar_ge1
  obtain ⟨θ_k, h_sparse, h_mse_k⟩ := hMaurey k hk_ge1
  have h_from_l0 := h_l0 θ_k
  have h_inter : MSE_37 fhat' f ≤
    2 * MSE_37 (Φ.mulVec θ') f + (2 * R ^ 2 / ↑k + 2 * (C_const * σ ^ 2 * L) * ↑k) + tail := by
    have h1 : 2 * MSE_37 (Φ.mulVec θ_k) f ≤
      2 * (MSE_37 (Φ.mulVec θ') f + R ^ 2 / ↑k) := by linarith
    have h_sparse_real : (support_size_37 θ_k : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast h_sparse
    have h2 : C_const * σ ^ 2 * ↑(support_size_37 θ_k) * Real.log (Real.exp 1 * ↑M) / ↑n ≤
      2 * (C_const * σ ^ 2 * L) * ↑k := by
      have h_assoc : C_const * σ ^ 2 * ↑(support_size_37 θ_k) * Real.log (Real.exp 1 * ↑M) / ↑n =
        C_const * σ ^ 2 * ↑(support_size_37 θ_k) * L := by
        rw [hL_def]; ring
      rw [h_assoc]
      have hCSL : 0 ≤ C_const * σ ^ 2 * L := by positivity
      nlinarith
    have h3 : 2 * (MSE_37 (Φ.mulVec θ') f + R ^ 2 / ↑k) =
      2 * MSE_37 (Φ.mulVec θ') f + 2 * (R ^ 2 / ↑k) := by ring
    have h4 : 2 * (R ^ 2 / ↑k) = 2 * R ^ 2 / ↑k := by ring
    linarith
  have h_alg := maurey_opt_algebra R σ C_const L (↑k) hR_pos hσ hC hL_pos hk_pos
    hk_le_kbar hk_ge_half hC_large
  linarith

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[MSE_34_eq_MSE_37](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma MSE_34_eq_MSE_37
  {n : ℕ}
  {fhat f : Fin n → ℝ} :
-- imply
  MSE_34 fhat f = MSE_37 fhat f := by
-- proof
  simp [MSE_34, MSE_37]

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[support_size_34_eq_37](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma support_size_34_eq_37
  {M : ℕ}
  {θ : Fin M → ℝ} :
-- imply
  support_size_34 θ = support_size_37 θ := by
-- proof
  simp [support_size_34, support_size_37]

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[abs_sum_mul_le_sqrt_mul_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma abs_sum_mul_le_sqrt_mul_sqrt
  {n : ℕ}
  {f g : Fin n → ℝ} :
-- imply
  |∑ i : Fin n, f i * g i| ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
-- proof
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (f i)))]
  exact Real.sqrt_le_sqrt h

end Rigollet.Chapter3

namespace Rigollet.Chapter3

/--
[cor_3_7_probabilistic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean)
-/
@[path]
lemma cor_3_7_probabilistic
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n M : ℕ}
  {Φ : Matrix (Fin n) (Fin M) ℝ}
  {f : Fin n → ℝ}
  {ε : Ω → Fin n → ℝ}
  {θhat : Ω → Fin M → ℝ}
  {σ : ℝ}
  {δ : ℝ}
-- given
  (hn : 0 < n)
  (hM : 0 < M)
  (hσ : 0 < σ)
  (hδ_pos : 0 < δ)
  (hδ_le : δ ≤ 1)
  (hsubG : IsSubGaussianNoiseMGF μ ε (σ ^ 2))
  (hBIC : ∀ ω θ, dotProduct (f + ε ω - Φ *ᵥ (θhat ω)) (f + ε ω - Φ *ᵥ (θhat ω)) + (16 * σ ^ 2 / (1/3)) * Real.log (6 * Real.exp 1 * ↑M) * ↑(support_size_34 (θhat ω)) ≤ dotProduct (f + ε ω - Φ *ᵥ θ) (f + ε ω - Φ *ᵥ θ) + (16 * σ ^ 2 / (1/3)) * Real.log (6 * Real.exp 1 * ↑M) * ↑(support_size_34 θ))
  (hNorm : DictNormalized Φ) :
-- imply
  ∃ C_const : ℝ, 0 < C_const ∧ μ {ω | ∀ θ : Fin M → ℝ, MSE_37 (Φ *ᵥ (θhat ω)) f ≤ 2 * MSE_37 (Φ *ᵥ θ) f + min (C_const * σ ^ 2 * ↑(support_size_37 θ) * (Real.log (Real.exp 1 * ↑M) / ↑n)) (C_const * σ * l1norm_37 θ * Real.sqrt (Real.log (Real.exp 1 * ↑M) / ↑n)) + C_const * σ ^ 2 * Real.log (1 / δ) / ↑n} ≥ ENNReal.ofReal (1 - δ) := by
-- proof
  have hα_pos : (0 : ℝ) < 1 / 3 := by norm_num
  have hα_lt : (1 : ℝ) / 3 < 1 := by norm_num
  obtain ⟨C₀, hC₀_pos, hprob⟩ := subG_bic_oracle_event hn hM Φ f ε θhat σ hσ
    (1/3) hα_pos hα_lt δ hδ_pos hδ_le hsubG hBIC
  have h_ratio : (1 + 1 / 3) / (1 - 1 / 3) = (2 : ℝ) := by norm_num
  have hlogM_pos : 0 < Real.log (Real.exp 1 * ↑M) := by
    apply Real.log_pos
    calc (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ = Real.exp 1 * 1 := (mul_one _).symm
      _ ≤ Real.exp 1 * ↑M := mul_le_mul_of_nonneg_left
        (Nat.one_le_cast.mpr hM) (le_of_lt (Real.exp_pos 1))
  set C_f := 4 * Real.sqrt (∑ i : Fin n, (f i) ^ 2) / (σ * Real.sqrt (Real.log (Real.exp 1 * ↑M))) with hC_f_def
  set C_new := max (max (9 * C₀ / 2) 36) (C_f + 1) with hC_new_def
  have hC_new_pos : 0 < C_new := by
    simp only [hC_new_def]
    exact lt_max_of_lt_left (lt_max_of_lt_right (by norm_num : (0 : ℝ) < 36))
  have hC_new_ge_36 : 36 ≤ C_new := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC_new_ge_C : 9 * C₀ / 2 ≤ C_new := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC_new_ge_Cf : C_f < C_new := lt_of_lt_of_le (lt_add_one C_f) (le_max_right _ _)
  refine ⟨C_new, hC_new_pos, ?_⟩
  apply le_trans hprob
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro θ
  have h_l0_34 := hω θ
  rw [h_ratio] at h_l0_34
  rw [MSE_34_eq_MSE_37, MSE_34_eq_MSE_37] at h_l0_34
  rw [support_size_34_eq_37] at h_l0_34
  have h_coeff_le : C₀ * σ ^ 2 / (1 / 3 * (1 - 1 / 3) * ↑n) ≤
    C_new * σ ^ 2 / ↑n := by
    rw [show (1 : ℝ) / 3 * (1 - 1 / 3) = 2 / 9 from by norm_num]
    rw [show C₀ * σ ^ 2 / (2 / 9 * ↑n) = 9 * C₀ / 2 * σ ^ 2 / ↑n from by ring]
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right hC_new_ge_C (sq_nonneg σ)
    · exact le_of_lt (Nat.cast_pos.mpr hn)
  have hlogM_ge_1 : 1 ≤ Real.log (Real.exp 1 * ↑M) := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Real.exp 1 * ↑M) := Real.log_le_log (Real.exp_pos 1)
        (le_mul_of_one_le_right (le_of_lt (Real.exp_pos 1)) (Nat.one_le_cast.mpr hM))
  have hlog_nonneg : 0 ≤ Real.log (Real.exp 1 * ↑M) := le_of_lt hlogM_pos
  have h_l0 : MSE_37 (Φ *ᵥ (θhat ω)) f ≤
    2 * MSE_37 (Φ *ᵥ θ) f +
    C_new * σ ^ 2 * ↑(support_size_37 θ) * (Real.log (Real.exp 1 * ↑M) / ↑n) +
    C_new * σ ^ 2 * Real.log (1 / δ) / ↑n := by
    have h1 : C₀ * σ ^ 2 / (1 / 3 * (1 - 1 / 3) * ↑n) *
      ↑(support_size_37 θ) * Real.log (Real.exp 1 * ↑M) ≤
      C_new * σ ^ 2 / ↑n *
        ↑(support_size_37 θ) * Real.log (Real.exp 1 * ↑M) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right h_coeff_le
        exact Nat.cast_nonneg _
      · exact hlog_nonneg
    have h2 : C₀ * σ ^ 2 / (1 / 3 * (1 - 1 / 3) * ↑n) *
      Real.log (1 / δ) ≤
      C_new * σ ^ 2 / ↑n * Real.log (1 / δ) := by
      apply mul_le_mul_of_nonneg_right h_coeff_le
      rw [one_div, Real.log_inv]
      linarith [Real.log_nonpos (le_of_lt hδ_pos) hδ_le]
    have heq1 : C_new * σ ^ 2 / ↑n * ↑(support_size_37 θ) * Real.log (Real.exp 1 * ↑M) =
      C_new * σ ^ 2 * ↑(support_size_37 θ) * (Real.log (Real.exp 1 * ↑M) / ↑n) := by
      ring
    have heq2 : C_new * σ ^ 2 / ↑n * Real.log (1 / δ) =
      C_new * σ ^ 2 * Real.log (1 / δ) / ↑n := by ring
    linarith
  set l0_term := C_new * σ ^ 2 * ↑(support_size_37 θ) *
    (Real.log (Real.exp 1 * ↑M) / ↑n)
  set l1_term := C_new * σ * l1norm_37 θ *
    Real.sqrt (Real.log (Real.exp 1 * ↑M) / ↑n)
  set tail := C_new * σ ^ 2 * Real.log (1 / δ) / ↑n
  obtain h_l0_le | h_l1_le := le_total l0_term l1_term
  ·
    rwa [min_eq_left h_l0_le]
  ·
    rw [min_eq_right h_l1_le]
    by_cases hR_lower : σ * Real.sqrt (C_new * (Real.log (Real.exp 1 * ↑M) / ↑n)) ≤ l1norm_37 θ
    ·
      have h_l0_all : ∀ θ' : Fin M → ℝ,
        MSE_37 (Φ *ᵥ (θhat ω)) f ≤
          2 * MSE_37 (Φ *ᵥ θ') f +
          C_new * σ ^ 2 * ↑(support_size_37 θ') *
            Real.log (Real.exp 1 * ↑M) / ↑n + tail := by
        intro θ'
        have h_l0_34' := hω θ'
        rw [h_ratio] at h_l0_34'
        rw [MSE_34_eq_MSE_37, MSE_34_eq_MSE_37] at h_l0_34'
        rw [support_size_34_eq_37] at h_l0_34'
        have h1 : C₀ * σ ^ 2 / (1 / 3 * (1 - 1 / 3) * ↑n) *
          ↑(support_size_37 θ') * Real.log (Real.exp 1 * ↑M) ≤
          C_new * σ ^ 2 / ↑n *
            ↑(support_size_37 θ') * Real.log (Real.exp 1 * ↑M) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_right h_coeff_le
            exact Nat.cast_nonneg _
          · exact hlog_nonneg
        have h2 : C₀ * σ ^ 2 / (1 / 3 * (1 - 1 / 3) * ↑n) *
          Real.log (1 / δ) ≤
          C_new * σ ^ 2 / ↑n * Real.log (1 / δ) := by
          apply mul_le_mul_of_nonneg_right h_coeff_le
          rw [one_div, Real.log_inv]
          linarith [Real.log_nonpos (le_of_lt hδ_pos) hδ_le]
        have heq1' : C_new * σ ^ 2 / ↑n * ↑(support_size_37 θ') * Real.log (Real.exp 1 * ↑M) =
          C_new * σ ^ 2 * ↑(support_size_37 θ') * Real.log (Real.exp 1 * ↑M) / ↑n := by
          ring
        have heq2' : C_new * σ ^ 2 / ↑n * Real.log (1 / δ) =
          C_new * σ ^ 2 * Real.log (1 / δ) / ↑n := by ring
        linarith
      have hMaurey_inst : ∀ k : ℕ, 1 ≤ k →
        ∃ θ' : Fin M → ℝ, support_size_37 θ' ≤ 2 * k ∧
          MSE_37 (Φ.mulVec θ') f ≤
            MSE_37 (Φ.mulVec θ) f + (l1norm_37 θ) ^ 2 / (k : ℝ) :=
        fun k hk => maurey_approximation_37 hn hM Φ f hNorm θ k hk
      exact maurey_three_case_bound hn hM Φ f hNorm σ hσ C_new hC_new_pos
        (Φ *ᵥ (θhat ω)) θ tail hMaurey_inst h_l0_all hC_new_ge_36 hR_lower
    ·
      push Not at hR_lower
      have h_l0_zero := hω (0 : Fin M → ℝ)
      rw [h_ratio] at h_l0_zero
      rw [MSE_34_eq_MSE_37, MSE_34_eq_MSE_37] at h_l0_zero
      rw [support_size_34_eq_37] at h_l0_zero
      have h_supp_zero : support_size_37 (0 : Fin M → ℝ) = 0 := by
        unfold support_size_37; simp
      have h_mul_zero : Φ *ᵥ (0 : Fin M → ℝ) = 0 := by
        ext i; simp [mulVec, dotProduct]
      rw [h_supp_zero, h_mul_zero] at h_l0_zero
      have h_zero_bound : MSE_37 (Φ *ᵥ (θhat ω)) f ≤
        2 * MSE_37 0 f + tail := by
        have : C₀ * σ ^ 2 / (1 / 3 * (1 - 1 / 3) * ↑n) * (0 : ℝ) *
          Real.log (Real.exp 1 * ↑M) = 0 := by ring
        have h2 : C₀ * σ ^ 2 / (1 / 3 * (1 - 1 / 3) * ↑n) *
          Real.log (1 / δ) ≤ C_new * σ ^ 2 / ↑n * Real.log (1 / δ) := by
          apply mul_le_mul_of_nonneg_right h_coeff_le
          rw [one_div, Real.log_inv]
          linarith [Real.log_nonpos (le_of_lt hδ_pos) hδ_le]
        have heq2 : C_new * σ ^ 2 / ↑n * Real.log (1 / δ) =
          C_new * σ ^ 2 * Real.log (1 / δ) / ↑n := by ring
        linarith
      suffices h_mse_diff : 2 * MSE_37 0 f ≤ 2 * MSE_37 (Φ *ᵥ θ) f + l1_term by
        linarith
      unfold MSE_37
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hl1_nonneg : 0 ≤ l1norm_37 θ :=
        Finset.sum_nonneg (fun i _ => abs_nonneg (θ i))
      have hL_nonneg : 0 ≤ Real.sqrt (Real.log (Real.exp 1 * ↑M) / ↑n) :=
        Real.sqrt_nonneg _
      have h_dot_bound : ∑ i : Fin n, f i * (Φ *ᵥ θ) i ≤
        Real.sqrt (∑ i : Fin n, (f i) ^ 2) * l1norm_37 θ * Real.sqrt (↑n) := by
        simp only [mulVec, dotProduct]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [show ∀ i j, f i * (Φ i j * θ j) = θ j * (f i * Φ i j) from fun i j => by ring]
        simp_rw [← Finset.mul_sum]
        calc ∑ j, θ j * ∑ i, f i * Φ i j
          ≤ ∑ j, |θ j * ∑ i, f i * Φ i j| :=
            Finset.sum_le_sum (fun j _ => le_abs_self _)
          _ = ∑ j, |θ j| * |∑ i, f i * Φ i j| := by
            congr 1; ext j; exact abs_mul _ _
          _ ≤ ∑ j, |θ j| * (Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, Φ i j ^ 2)) := by
            apply Finset.sum_le_sum; intro j _
            exact mul_le_mul_of_nonneg_left
              (abs_sum_mul_le_sqrt_mul_sqrt f (fun i => Φ i j)) (abs_nonneg _)
          _ ≤ ∑ j, |θ j| * (Real.sqrt (∑ i, f i ^ 2) * Real.sqrt ↑n) := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hNorm j)) (Real.sqrt_nonneg _)
          _ = Real.sqrt (∑ i, f i ^ 2) * l1norm_37 θ * Real.sqrt ↑n := by
            unfold l1norm_37; simp_rw [← Finset.sum_mul]; ring
      have h_Cf_bound : 4 * Real.sqrt (∑ i : Fin n, (f i) ^ 2) ≤
        C_new * σ * Real.sqrt (Real.log (Real.exp 1 * ↑M)) := by
        have hsqrt_pos : 0 < Real.sqrt (Real.log (Real.exp 1 * ↑M)) :=
          Real.sqrt_pos_of_pos hlogM_pos
        have h1 : C_f * (σ * Real.sqrt (Real.log (Real.exp 1 * ↑M))) =
          4 * Real.sqrt (∑ i : Fin n, (f i) ^ 2) := by
          rw [hC_f_def]
          field_simp
        have h2 : C_f < C_new := hC_new_ge_Cf
        have h3 : 0 < σ * Real.sqrt (Real.log (Real.exp 1 * ↑M)) :=
          mul_pos hσ hsqrt_pos
        calc 4 * Real.sqrt (∑ i : Fin n, (f i) ^ 2)
          = C_f * (σ * Real.sqrt (Real.log (Real.exp 1 * ↑M))) := h1.symm
          _ ≤ C_new * (σ * Real.sqrt (Real.log (Real.exp 1 * ↑M))) :=
            mul_le_mul_of_nonneg_right (le_of_lt h2) (le_of_lt h3)
          _ = C_new * σ * Real.sqrt (Real.log (Real.exp 1 * ↑M)) := by ring
      simp only [Pi.zero_apply, zero_sub, neg_sq]
      set g := (Φ *ᵥ θ) with hg_def
      suffices h : 2 * (1 / ↑n) * (∑ i, f i ^ 2 - ∑ i, (g i - f i) ^ 2) ≤ l1_term by
        linarith
      have h_diff : ∑ i : Fin n, f i ^ 2 - ∑ i : Fin n, (g i - f i) ^ 2 =
        ∑ i : Fin n, (2 * f i * g i - g i ^ 2) := by
        rw [← Finset.sum_sub_distrib]; congr 1; ext i; ring
      rw [h_diff]
      have h_drop : ∑ i : Fin n, (2 * f i * g i - g i ^ 2) ≤
        2 * ∑ i : Fin n, f i * g i := by
        calc ∑ i, (2 * f i * g i - g i ^ 2)
          ≤ ∑ i, (2 * (f i * g i)) :=
            Finset.sum_le_sum (fun i _ => by linarith [sq_nonneg (g i)])
          _ = 2 * ∑ i, f i * g i := by rw [Finset.mul_sum]
      have h_step1 : 2 * (1 / ↑n) * ∑ i, (2 * f i * g i - g i ^ 2) ≤
        4 * (1 / ↑n) * ∑ i, f i * g i := by nlinarith [show (0 : ℝ) ≤ 1 / ↑n from by positivity]
      have h_step2 : 4 * (1 / ↑n) * ∑ i, f i * g i ≤
        4 * (1 / ↑n) * (Real.sqrt (∑ i, f i ^ 2) * l1norm_37 θ * Real.sqrt ↑n) := by
        apply mul_le_mul_of_nonneg_left h_dot_bound (by positivity : (0 : ℝ) ≤ 4 * (1 / ↑n))
      have h_sqrt_n : Real.sqrt ↑n / ↑n = 1 / Real.sqrt ↑n := by
        have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos.mpr hn_pos
        rw [div_eq_div_iff hn_pos.ne' hsqrt_pos.ne', one_mul]
        exact Real.mul_self_sqrt hn_pos.le
      have h_sqrt_div : Real.sqrt (Real.log (Real.exp 1 * ↑M)) / Real.sqrt ↑n =
        Real.sqrt (Real.log (Real.exp 1 * ↑M) / ↑n) := by
        rw [← Real.sqrt_div hlog_nonneg]
      calc 2 * (1 / ↑n) * ∑ i, (2 * f i * g i - g i ^ 2)
        ≤ 4 * (1 / ↑n) * (Real.sqrt (∑ i, f i ^ 2) * l1norm_37 θ * Real.sqrt ↑n) :=
          by linarith
        _ = 4 * Real.sqrt (∑ i : Fin n, f i ^ 2) * l1norm_37 θ * (Real.sqrt ↑n / ↑n) := by ring
        _ = 4 * Real.sqrt (∑ i : Fin n, f i ^ 2) * l1norm_37 θ * (1 / Real.sqrt ↑n) := by
          rw [h_sqrt_n]
        _ = (4 * Real.sqrt (∑ i : Fin n, f i ^ 2)) * (l1norm_37 θ / Real.sqrt ↑n) := by ring
        _ ≤ (C_new * σ * Real.sqrt (Real.log (Real.exp 1 * ↑M))) * (l1norm_37 θ / Real.sqrt ↑n) := by
          apply mul_le_mul_of_nonneg_right h_Cf_bound
          exact div_nonneg hl1_nonneg (Real.sqrt_nonneg _)
        _ = C_new * σ * l1norm_37 θ * (Real.sqrt (Real.log (Real.exp 1 * ↑M)) / Real.sqrt ↑n) :=
          by ring
        _ = C_new * σ * l1norm_37 θ * Real.sqrt (Real.log (Real.exp 1 * ↑M) / ↑n) := by
          rw [h_sqrt_div]
        _ = l1_term := by rfl

end Rigollet.Chapter3


-- created on 2026-10-23
