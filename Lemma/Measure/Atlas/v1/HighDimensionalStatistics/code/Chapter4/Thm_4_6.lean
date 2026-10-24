import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_6
open MeasureTheory ProbabilityTheory Matrix Real Finset BigOperators Rigollet Rigollet.Chapter4 Rigollet.Chapter4.Thm_4_6


namespace Rigollet.Chapter4.Thm_4_6

/--
[opnorm_le_of_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma opnorm_le_of_bound
  {d : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ}
  {M : ℝ}
-- given
  (hM : 0 ≤ M)
  (h : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 → ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖ ≤ M) :
-- imply
  matrixOpNorm A ≤ M := by
-- proof
  apply ciSup_le; intro v
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv]; exact h v hv
  · rw [ciSup_neg hv, Real.sSup_empty]; exact hM

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[matrixOpNorm_le_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma matrixOpNorm_le_root
  {d : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ} :
-- imply
  matrixOpNorm A ≤ _root_.matrixOpNorm A := by
-- proof
  unfold matrixOpNorm _root_.matrixOpNorm
  apply ciSup_le; intro v
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv]
    have heq : (EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v) =
      Matrix.toEuclideanLin A v := rfl
    rw [heq]
    calc ‖Matrix.toEuclideanLin A v‖
      = ‖(Matrix.toEuclideanLin A).toContinuousLinearMap v‖ := rfl
      _ ≤ ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ := by rw [hv, mul_one]
  · rw [ciSup_neg hv]
    exact Real.sSup_empty ▸ norm_nonneg _

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[norm_plain_le_euclidean_loc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma norm_plain_le_euclidean_loc
  {d : ℕ}
  {x : EuclideanSpace ℝ (Fin d)}
-- given
  (hx : ‖x‖ ≤ 1) :
-- imply
  ‖(fun j => x j : Fin d → ℝ)‖ ≤ 1 := by
-- proof
  apply pi_norm_le_iff_of_nonneg (by linarith) |>.mpr
  intro j
  calc ‖x j‖ = |x.ofLp j| := rfl
    _ ≤ √(∑ i, ‖x.ofLp i‖ ^ 2) := by
      rw [Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      calc |x.ofLp j| ^ 2 = ‖x.ofLp j‖ ^ 2 := by rw [Real.norm_eq_abs]
        _ ≤ ∑ i, ‖x.ofLp i‖ ^ 2 := by
          apply Finset.single_le_sum (f := fun i => ‖x.ofLp i‖ ^ 2)
          · intro i _; exact sq_nonneg _
          · exact Finset.mem_univ j
    _ = ‖x‖ := (EuclideanSpace.norm_eq x).symm
    _ ≤ 1 := hx

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[eps_net_opnorm_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma eps_net_opnorm_reduction
  {d : ℕ}
-- given
  (hd : 0 < d) :
-- imply
  ∃ (N : Finset (Fin d → ℝ)), (N.card : ℝ) ≤ (12 : ℝ) ^ d ∧ N.Nonempty ∧ (∀ x ∈ N, ‖x‖ ≤ 1) ∧ (∀ (A : Matrix (Fin d) (Fin d) ℝ) (t : ℝ), matrixOpNorm A > t → ∃ x ∈ N, ∃ y ∈ N, |dotProduct x (A.mulVec y)| > t / 2) := by
-- proof
  have hε_pos : (0 : ℝ) < 1 / 4 := by norm_num
  have hε_lt : (1 : ℝ) / 4 < 1 := by norm_num
  obtain ⟨N_L2, hN_net, hN_card⟩ := lemma_1_18_covering_number_euclidean_ball hd (1/4) hε_pos hε_lt
  let N : Finset (Fin d → ℝ) := N_L2.image (EuclideanSpace.equiv (Fin d) ℝ)
  have hN_sub_L2 : ∀ x ∈ N_L2, ‖x‖ ≤ 1 := by
    intro x hx
    have := hN_net.subset_set (Finset.mem_coe.mpr hx)
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hN_cover : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
    ∃ x ∈ N_L2, dist u x ≤ 1/4 := by
    intro u hu
    have hu_ball : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith [hu.symm.le]
    obtain ⟨x, hxN, hdist⟩ := hN_net.exists_dist_le hu_ball
    exact ⟨x, Finset.mem_coe.mp hxN, dist_comm x u ▸ hdist⟩
  have hN_ne_L2 : N_L2.Nonempty := by
    have : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_closedBall]; simp
    obtain ⟨x, hxN, _⟩ := hN_net.exists_dist_le this
    exact ⟨x, Finset.mem_coe.mp hxN⟩
  have hN_ne : N.Nonempty := hN_ne_L2.image _
  have hN_card_bound : (N.card : ℝ) ≤ (12 : ℝ) ^ d := by
    have h1 : N.card ≤ N_L2.card := Finset.card_image_le
    have h12 : (3 : ℝ) / (1 / 4) = 12 := by norm_num
    have h12d : ((3 : ℝ) / (1 / 4)) ^ d = (12 : ℝ) ^ d := by rw [h12]
    calc (N.card : ℝ) ≤ (N_L2.card : ℝ) := Nat.cast_le.mpr h1
      _ ≤ ↑(Nat.ceil ((3 / (1/4)) ^ d)) := Nat.cast_le.mpr hN_card
      _ = ↑(Nat.ceil ((12 : ℝ) ^ d)) := by rw [h12d]
      _ = (12 : ℝ) ^ d := by
        have h12' : (12 : ℝ) = ↑(12 : ℕ) := by norm_num
        conv_lhs => rw [h12', ← Nat.cast_pow, Nat.ceil_natCast, Nat.cast_pow, ← h12']
  have hN_norm : ∀ x ∈ N, ‖x‖ ≤ 1 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact norm_plain_le_euclidean_loc y (hN_sub_L2 y hy)
  refine ⟨N, hN_card_bound, hN_ne, hN_norm, ?_⟩
  intro A t hAt
  by_contra h_neg
  push Not at h_neg
  have h_bound : ∀ x ∈ N_L2, ∀ y ∈ N_L2,
    dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
      (A.mulVec (EuclideanSpace.equiv (Fin d) ℝ y)) ≤ t / 2 := by
    intro x hx y hy
    have hxN : EuclideanSpace.equiv (Fin d) ℝ x ∈ N := Finset.mem_image_of_mem _ hx
    have hyN : EuclideanSpace.equiv (Fin d) ℝ y ∈ N := Finset.mem_image_of_mem _ hy
    exact le_of_abs_le (h_neg _ hxN _ hyN)
  have h42 : _root_.matrixOpNorm A ≤ 2 * (t / 2) :=
    lemma_4_2_eps_net_reduction A hN_cover hN_cover hN_sub_L2 hN_sub_L2 hN_ne_L2 hN_ne_L2
      (t / 2) h_bound
  have h_bridge := matrixOpNorm_le_root A
  linarith

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[dotProduct_outer_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma dotProduct_outer_mulVec
  {d : ℕ}
  {x y v : Fin d → ℝ} :
-- imply
  dotProduct x ((Matrix.of (fun j k => v j * v k)).mulVec y) = dotProduct x v * dotProduct v y := by
-- proof
  simp only [dotProduct, mulVec, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext k; congr 1; ext j; ring

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[polarization_dotProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma polarization_dotProduct
  {d : ℕ}
  {x y v : Fin d → ℝ} :
-- imply
  dotProduct x v * dotProduct v y = ((dotProduct (x + y) v) ^ 2 - (dotProduct (x - y) v) ^ 2) / 4 := by
-- proof
  have hxp : dotProduct (x + y) v = dotProduct x v + dotProduct y v := by
    simp [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hxm : dotProduct (x - y) v = dotProduct x v - dotProduct y v := by
    simp [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hcomm : dotProduct v y = dotProduct y v := by
    simp [dotProduct]; congr 1; ext i; ring
  rw [hxp, hxm, hcomm]; ring

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[bilinear_form_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma bilinear_form_decomposition
  {d : ℕ}
  {d : ℕ}
  {n : ℕ}
  {Y : Fin n → Ω → Fin d → ℝ}
  {ω : Ω}
  {x y : Fin d → ℝ}
-- given
  (hn : 0 < n) :
-- imply
  dotProduct x ((empiricalCovariance Y ω - 1).mulVec y) = (↑n)⁻¹ * ∑ i : Fin n, ((∑ j : Fin d, x j * Y i ω j) * (∑ k : Fin d, Y i ω k * y k) - dotProduct x y) := by
-- proof
  simp only [empiricalCovariance, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  simp only [Matrix.sum_mulVec, dotProduct_sum]
  rw [one_div, Matrix.one_mulVec]
  have h2 : ∀ i : Fin n,
    x ⬝ᵥ (of fun j k => Y i ω j * Y i ω k).mulVec y =
    (∑ j, x j * Y i ω j) * (∑ k, Y i ω k * y k) := by
    intro i
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]; congr 1; ext k; congr 1; ext j; ring
  simp_rw [h2]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  field_simp

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[subgaussianvec_projection_is_subgaussian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma subgaussianvec_projection_is_subgaussian
  {d : ℕ}
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {Y : Ω → Fin d → ℝ}
  {σsq : ℝ}
  {u : EuclideanSpace ℝ (Fin d)}
-- given
  (hSubG : IsSubGaussianVec μ Y σsq)
  (hu : ‖u‖ = 1)
  (hInt : Integrable (fun ω => ∑ j, u j * Y ω j) μ)
  (hMean : ∫ ω, (∑ j, u j * Y ω j) ∂μ = 0)
  (hExpInt : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * ∑ j, u j * Y ω j)) μ) :
-- imply
  IsSubGaussian (fun ω => ∑ j, u j * Y ω j) σsq μ :=
-- proof
  ⟨hInt, hMean, hExpInt, fun s => hSubG.2.1 u hu s⟩

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[polarization_product_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma polarization_product_eq
  {d : ℕ}
  {x y z : Fin d → ℝ} :
-- imply
  (∑ j, x j * z j) * (∑ k, z k * y k) = ((∑ j, (x + y) j * z j) ^ 2 - (∑ j, (x - y) j * z j) ^ 2) / 4 :=
-- proof
  polarization_dotProduct x y z

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[nfold_exp_integral_factoring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma nfold_exp_integral_factoring
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {f : Fin n → Ω → ℝ}
  {s : Fin n → ℝ}
-- given
  (hIndepFun : iIndepFun (m := fun _ => inferInstance) f μ)
  (hMeas : ∀ i, AEMeasurable (f i) μ) :
-- imply
  ∫ ω, ∏ i : Fin n, Real.exp (s i * f i ω) ∂μ = ∏ i : Fin n, ∫ ω, Real.exp (s i * f i ω) ∂μ :=
-- proof
  hIndepFun.integral_fun_prod_comp (f := fun i => fun x => Real.exp (s i * x)) hMeas
    (fun _ => (Measurable.exp (measurable_const.mul measurable_id)).aestronglyMeasurable)

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[exp_individual_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma exp_individual_integrable
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {f : Fin n → Ω → ℝ}
  {b : ℝ}
  {i : Fin n}
  {s : ℝ}
-- given
  (h_mgf : ∀ i s, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * f i ω)) ∂μ ≤ ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)))
  (hMeas : ∀ i, AEStronglyMeasurable (f i) μ) :
-- imply
  Integrable (fun ω => Real.exp (s * f i ω)) μ := by
-- proof
  constructor
  ·
    have : (fun ω => Real.exp (s * f i ω)) = Real.exp ∘ (fun ω => s * f i ω) := rfl
    rwa [this]
      ((aestronglyMeasurable_const.mul (hMeas i)))
  ·
    change ∫⁻ a, ↑‖Real.exp (s * f i a)‖₊ ∂μ < ⊤
    calc ∫⁻ a, ↑‖Real.exp (s * f i a)‖₊ ∂μ
      = ∫⁻ a, ENNReal.ofReal (Real.exp (s * f i a)) ∂μ := by
        congr 1; ext ω
        simp [ENNReal.ofReal, Real.toNNReal_eq_nnnorm_of_nonneg (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)) := h_mgf i s
      _ < ⊤ := ENNReal.ofReal_lt_top

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[average_exp_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma average_exp_integrable
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {f : Fin n → Ω → ℝ}
  {b : ℝ}
  {l : ℝ}
-- given
  (hn : 0 < n)
  (h_mgf : ∀ i s, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * f i ω)) ∂μ ≤ ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)))
  (hIndepFun : iIndepFun (m := fun _ => inferInstance) f μ)
  (hMeas : ∀ i, AEMeasurable (f i) μ) :
-- imply
  Integrable (fun ω => Real.exp (l * ((↑n)⁻¹ * ∑ i : Fin n, f i ω))) μ := by
-- proof
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hn_inv_pos : (0 : ℝ) < (↑n : ℝ)⁻¹ := inv_pos_of_pos hn_pos
  have hf_aesm : ∀ i, AEStronglyMeasurable (f i) μ :=
    fun i => (hMeas i).aestronglyMeasurable
  have h_int : ∀ i s, Integrable (fun ω => Real.exp (s * f i ω)) μ :=
    fun i s => exp_individual_integrable μ n f b h_mgf hf_aesm i s
  have h_target_aesm : AEStronglyMeasurable
    (fun ω => Real.exp (l * ((↑n : ℝ)⁻¹ * ∑ i, f i ω))) μ := by
    apply Continuous.comp_aestronglyMeasurable
      (by fun_prop : Continuous (fun x : ℝ => Real.exp (l * ((↑n : ℝ)⁻¹ * x))))
    have : (fun ω => ∑ i : Fin n, f i ω) = (∑ i : Fin n, f i) := by
      ext ω; simp [Finset.sum_apply]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ (fun i _ => hf_aesm i)
  have h_dom_int : Integrable (fun ω => (↑n : ℝ)⁻¹ * ∑ i, Real.exp (l * f i ω)) μ := by
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro i _
    exact h_int i l
  have h_bound : ∀ᵐ ω ∂μ, ‖Real.exp (l * ((↑n : ℝ)⁻¹ * ∑ i, f i ω))‖ ≤
    ‖(↑n : ℝ)⁻¹ * ∑ i, Real.exp (l * f i ω)‖ := by
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg' n))
      (Finset.sum_nonneg (fun i _ => le_of_lt (exp_pos _))))]
    have hsum_eq : l * ((↑n : ℝ)⁻¹ * ∑ i, f i ω) =
      ∑ i : Fin n, (↑n : ℝ)⁻¹ • (l * f i ω) := by
      simp only [smul_eq_mul, Finset.mul_sum]
      congr 1; ext i; ring
    rw [hsum_eq]
    have hsum_dom : (↑n : ℝ)⁻¹ * ∑ i, Real.exp (l * f i ω) =
      ∑ i : Fin n, (↑n : ℝ)⁻¹ • Real.exp (l * f i ω) := by
      simp [smul_eq_mul, Finset.mul_sum]
    rw [hsum_dom]
    exact ConvexOn.map_sum_le convexOn_exp
      (fun i _ => le_of_lt hn_inv_pos)
      (by simp [Finset.sum_const]; field_simp)
      (fun i _ => Set.mem_univ _)
  exact h_dom_int.mono h_target_aesm h_bound

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[average_mgf_from_independence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma average_mgf_from_independence
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {f : Fin n → Ω → ℝ}
  {b : ℝ}
  {l : ℝ}
-- given
  (hn : 0 < n)
  (h_mgf : ∀ i s, ∫ ω, Real.exp (s * f i ω) ∂μ ≤ Real.exp (b ^ 2 * s ^ 2 / 2))
  (h_mgf_lint : ∀ i s, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * f i ω)) ∂μ ≤ ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)))
  (hIndepFun : iIndepFun (m := fun _ => inferInstance) f μ)
  (hMeas : ∀ i, AEMeasurable (f i) μ) :
-- imply
  (∫ ω, Real.exp (l * ((↑n)⁻¹ * ∑ i : Fin n, f i ω)) ∂μ ≤ Real.exp (b ^ 2 * l ^ 2 / (2 * ↑n))) ∧ Integrable (fun ω => Real.exp (l * ((↑n)⁻¹ * ∑ i : Fin n, f i ω))) μ := by
-- proof
  constructor
  ·
    simp_rw [show ∀ ω, l * ((↑n : ℝ)⁻¹ * ∑ i, f i ω) =
      ∑ i, (l * (↑n : ℝ)⁻¹) * f i ω from fun ω => by simp [Finset.mul_sum, mul_assoc], exp_sum]
    rw [nfold_exp_integral_factoring μ n f (fun _ => l * (↑n : ℝ)⁻¹) hIndepFun hMeas]
    calc ∏ i : Fin n, ∫ ω, Real.exp (l * (↑n : ℝ)⁻¹ * f i ω) ∂μ
      ≤ ∏ _i : Fin n, Real.exp (b ^ 2 * (l * (↑n : ℝ)⁻¹) ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => integral_nonneg fun ω => (Real.exp_pos _).le)
          (fun i _ => h_mgf i _)
      _ = Real.exp (b ^ 2 * l ^ 2 / (2 * ↑n)) := by
        simp only [Finset.prod_const, Finset.card_fin, ← Real.exp_nat_mul]
        congr 1
        have hn' : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
        field_simp
  ·
    exact average_exp_integrable μ n hn f b h_mgf_lint hIndepFun hMeas l

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[subgaussian_vec_aemeasurable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma subgaussian_vec_aemeasurable
  {d : ℕ}
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {Y : Ω → Fin d → ℝ}
  {σ : ℝ}
-- given
  (hSubG : IsSubGaussianVec μ Y σ) :
-- imply
  AEMeasurable Y μ :=
-- proof
  hSubG.1

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[chernoff_from_mgf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma chernoff_from_mgf
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {f : Ω → ℝ}
  {b : ℝ}
  {s : ℝ}
-- given
  (hn : 0 < n)
  (hb : 0 < b)
  (hmgf : ∀ l, ∫ ω, Real.exp (l * f ω) ∂μ ≤ Real.exp (b ^ 2 * l ^ 2 / (2 * ↑n)))
  (h_int : ∀ l, Integrable (fun ω => Real.exp (l * f ω)) μ)
  (hs : 0 < s) :
-- imply
  μ {ω : Ω | |f ω| > s} ≤ ENNReal.ofReal (2 * Real.exp (-(↑n / 2 * min ((s / b) ^ 2) (s / b)))) := by
-- proof
  have hn_pos : (0 : ℝ) < (↑n : ℝ) := Nat.cast_pos.mpr hn
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  set C := Real.exp (-(↑n * s ^ 2 / (2 * b ^ 2)))
  have hC_pos : 0 < C := Real.exp_pos _
  have h_upper : μ.real {ω | s ≤ f ω} ≤ C := by
    calc μ.real {ω | s ≤ f ω}
      ≤ Real.exp (-(↑n * s / b ^ 2) * s) * mgf f μ (↑n * s / b ^ 2) :=
        measure_ge_le_exp_mul_mgf s (by positivity) (h_int _)
      _ ≤ Real.exp (-(↑n * s / b ^ 2) * s) *
        Real.exp (b ^ 2 * (↑n * s / b ^ 2) ^ 2 / (2 * ↑n)) := by
        gcongr; exact hmgf _
      _ = Real.exp (-(↑n * s / b ^ 2) * s +
        b ^ 2 * (↑n * s / b ^ 2) ^ 2 / (2 * ↑n)) := by rw [← Real.exp_add]
      _ = C := by congr 1; field_simp; ring
  have h_lower : μ.real {ω | s ≤ -f ω} ≤ C := by
    have hmgf_neg : ∀ l, mgf (fun ω => -f ω) μ l ≤
      Real.exp (b ^ 2 * l ^ 2 / (2 * ↑n)) := by
      intro l; show ∫ ω, Real.exp (l * -f ω) ∂μ ≤ _
      simp_rw [mul_neg, ← neg_mul]
      have := hmgf (-l); simp only [neg_sq] at this; exact this
    calc μ.real {ω | s ≤ -f ω}
      ≤ Real.exp (-(↑n * s / b ^ 2) * s) *
        mgf (fun ω => -f ω) μ (↑n * s / b ^ 2) := by
        exact measure_ge_le_exp_mul_mgf s (by positivity)
          (by simp only [mul_neg, ← neg_mul]; exact h_int _)
      _ ≤ Real.exp (-(↑n * s / b ^ 2) * s) *
        Real.exp (b ^ 2 * (↑n * s / b ^ 2) ^ 2 / (2 * ↑n)) := by
        gcongr; exact hmgf_neg _
      _ = Real.exp (-(↑n * s / b ^ 2) * s +
        b ^ 2 * (↑n * s / b ^ 2) ^ 2 / (2 * ↑n)) := by rw [← Real.exp_add]
      _ = C := by congr 1; field_simp; ring
  have h_subset : {ω : Ω | |f ω| > s} ⊆ {ω | s ≤ f ω} ∪ {ω | s ≤ -f ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, gt_iff_lt] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    cases abs_cases (f ω) with
    | inl h => left; linarith [h.1]
    | inr h => right; linarith [h.1]
  have h_C_le : C ≤ Real.exp (-(↑n / 2 * min ((s / b) ^ 2) (s / b))) := by
    apply Real.exp_le_exp.mpr
    have : ↑n * s ^ 2 / (2 * b ^ 2) = ↑n / 2 * (s / b) ^ 2 := by field_simp
    rw [this]
    nlinarith [min_le_left ((s / b) ^ 2) (s / b), show (0 : ℝ) < ↑n / 2 from by linarith]
  calc μ {ω | |f ω| > s}
    ≤ μ ({ω | s ≤ f ω} ∪ {ω | s ≤ -f ω}) := measure_mono h_subset
    _ ≤ μ {ω | s ≤ f ω} + μ {ω | s ≤ -f ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := by
      gcongr
      · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hC_pos.le).mpr
        (Measure.real_def μ _ ▸ h_upper)
      · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hC_pos.le).mpr
        (Measure.real_def μ _ ▸ h_lower)
    _ = ENNReal.ofReal (2 * C) := by
      rw [← ENNReal.ofReal_add hC_pos.le hC_pos.le]; congr 1; ring
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(↑n / 2 * min ((s / b) ^ 2) (s / b)))) := by
      apply ENNReal.ofReal_le_ofReal; linarith [h_C_le]

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[half_div16_eq_div32](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma half_div16_eq_div32
  {d : ℕ}
  {t : ℝ} :
-- imply
  min ((t / 2 / 16) ^ 2) (t / 2 / 16) = min ((t / 32) ^ 2) (t / 32) := by
-- proof
  congr 1 <;> ring

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[two_card_sq_le_288d](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma two_card_sq_le_288d
  {d : ℕ}
  {N : Finset α}
-- given
  (hd : 0 < d)
  (hN : (N.card : ℝ) ≤ (12 : ℝ) ^ d) :
-- imply
  2 * (N.card : ℝ) ^ 2 ≤ (288 : ℝ) ^ d := by
-- proof
  have h1 : (N.card : ℝ) ^ 2 ≤ (144 : ℝ) ^ d := by
    calc (N.card : ℝ) ^ 2 ≤ ((12 : ℝ) ^ d) ^ 2 := by
      apply sq_le_sq'
      · linarith [Nat.cast_nonneg (α := ℝ) N.card]
      · exact hN
      _ = (144 : ℝ) ^ d := by
        rw [← pow_mul, show d * 2 = 2 * d from by ring, pow_mul,
          show (12 : ℝ) ^ 2 = 144 from by norm_num]
  calc 2 * (N.card : ℝ) ^ 2 ≤ 2 * (144 : ℝ) ^ d := by linarith
    _ ≤ 2 ^ d * (144 : ℝ) ^ d := by
      gcongr
      exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    _ = (288 : ℝ) ^ d := by rw [← mul_pow]; norm_num

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[posdef_whitening_matrix_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma posdef_whitening_matrix_exists
  {d : ℕ}
  {covMat : Matrix (Fin d) (Fin d) ℝ}
-- given
  (hPD : covMat.PosDef) :
-- imply
  ∃ (S : Matrix (Fin d) (Fin d) ℝ), S * covMat * S.transpose = 1 := by
-- proof
  classical
  open scoped MatrixOrder in
  let R := CFC.sqrt covMat
  have hR_unit : IsUnit R := by
    open scoped MatrixOrder in
    exact (CFC.isUnit_sqrt_iff covMat hPD.posSemidef.nonneg).mpr hPD.isUnit
  use R⁻¹
  have hRsq : R ^ 2 = covMat := by
    open scoped MatrixOrder in exact CFC.sq_sqrt covMat hPD.posSemidef.nonneg
  have hR_sa : IsSelfAdjoint R := by
    open scoped MatrixOrder in
    exact (CFC.sqrt_nonneg covMat).posSemidef.isHermitian.isSelfAdjoint
  have hR_symm : R.transpose = R := by
    have := hR_sa.star_eq
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hRinv_symm : R⁻¹.transpose = R⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial, conjTranspose_nonsing_inv,
      conjTranspose_eq_transpose_of_trivial, hR_symm]
  rw [hRinv_symm, ← hRsq, sq]
  obtain ⟨u, hu⟩ := hR_unit
  rw [← hu]; simp

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[covQuadForm_eq_dotProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma covQuadForm_eq_dotProduct
  {d : ℕ}
  {covMat : Matrix (Fin d) (Fin d) ℝ}
  {v : Fin d → ℝ} :
-- imply
  covQuadForm covMat v = dotProduct v (covMat.mulVec v) := by
-- proof
  simp only [covQuadForm, dotProduct, mulVec]
  congr 1; ext j
  simp only [Finset.mul_sum]
  congr 1; ext k; ring

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[subgaussian_whitening_preservation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma subgaussian_whitening_preservation
  {d : ℕ}
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → Fin d → ℝ}
  {S covMat : Matrix (Fin d) (Fin d) ℝ}
-- given
  (hSG : IsSubGaussianVec μ X (matrixOpNorm covMat))
  (hcov : ∀ (j k : Fin d), ∫ ω, X ω j * X ω k ∂μ = covMat j k)
  (hWhiten : S * covMat * S.transpose = 1)
  (hDir : ∀ (w : Fin d → ℝ) (s : ℝ), ∫ ω, Real.exp (s * (∑ j : Fin d, w j * X ω j)) ∂μ ≤ Real.exp (dotProduct w (covMat.mulVec w) * s ^ 2 / 2))
  (hDirL : ∀ (w : Fin d → ℝ) (s : ℝ), ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (∑ j : Fin d, w j * X ω j))) ∂μ ≤ ENNReal.ofReal (Real.exp (dotProduct w (covMat.mulVec w) * s ^ 2 / 2))) :
-- imply
  IsSubGaussianVec μ (fun ω => S.mulVec (X ω)) 1 := by
-- proof
  obtain ⟨hMeas, _, _⟩ := hSG
  have hMeasSX : AEMeasurable (fun ω => S.mulVec (X ω)) μ := by
    have heq : (fun ω => S.mulVec (X ω)) = S.mulVecLin ∘ X := by ext ω; simp
    rw [heq]
    exact (LinearMap.continuous_of_finiteDimensional S.mulVecLin).measurable.comp_aemeasurable hMeas
  have hsum_rw : ∀ (u : EuclideanSpace ℝ (Fin d)) (ω : Ω),
    ∑ j : Fin d, u.ofLp j * (S.mulVec (X ω)) j =
    ∑ k : Fin d, (S.transpose.mulVec u.ofLp) k * X ω k := by
    intro u ω
    simp only [mulVec, dotProduct, transpose_apply]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1; ext j; congr 1; ext k; ring
  have hqf_eq : ∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    dotProduct (S.transpose.mulVec u.ofLp) (covMat.mulVec (S.transpose.mulVec u.ofLp)) = 1 := by
    intro u hu
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    rw [show vecMul u.ofLp S = S.transpose.mulVec u.ofLp
      from (mulVec_transpose S u.ofLp).symm]
    rw [dotProduct_mulVec (vecMul u.ofLp (S * covMat)) S.transpose u.ofLp]
    rw [vecMul_vecMul]
    rw [← dotProduct_mulVec u.ofLp (S * covMat * S.transpose) u.ofLp]
    rw [hWhiten, one_mulVec]
    have h : Real.sqrt (∑ i : Fin d, ‖u i‖ ^ 2) = 1 := by
      rw [← EuclideanSpace.norm_eq]; exact hu
    have hnn : (0 : ℝ) ≤ ∑ i : Fin d, ‖u i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) _)
    have h2 : (∑ i : Fin d, ‖u i‖ ^ 2 : ℝ) = 1 := by nlinarith [Real.sq_sqrt hnn]
    simp only [dotProduct]
    convert h2 using 1
    congr 1; ext i; rw [Real.norm_eq_abs, sq_abs, sq]
  refine ⟨hMeasSX, ?_, ?_⟩
  · intro u hu s
    simp_rw [hsum_rw u]
    calc ∫ ω, Real.exp (s * ∑ j, (S.transpose.mulVec u.ofLp) j * X ω j) ∂μ
      ≤ Real.exp (dotProduct (S.transpose.mulVec u.ofLp)
        (covMat.mulVec (S.transpose.mulVec u.ofLp)) * s ^ 2 / 2) :=
        hDir _ s
      _ = Real.exp (1 * s ^ 2 / 2) := by rw [hqf_eq u hu]
  · intro u hu s
    simp_rw [hsum_rw u]
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (s * ∑ j, (S.transpose.mulVec u.ofLp) j * X ω j)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (dotProduct (S.transpose.mulVec u.ofLp)
        (covMat.mulVec (S.transpose.mulVec u.ofLp)) * s ^ 2 / 2)) :=
        hDirL _ s
      _ = ENNReal.ofReal (Real.exp (1 * s ^ 2 / 2)) := by rw [hqf_eq u hu]

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[matrixOpNorm_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma matrixOpNorm_bddAbove
  {d : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ} :
-- imply
  BddAbove (Set.range (fun v : EuclideanSpace ℝ (Fin d) => ⨆ (_ : ‖v‖ = 1), ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖)) := by
-- proof
  use ‖(toEuclideanLin A).toContinuousLinearMap‖
  intro x hx
  obtain ⟨v, rfl⟩ := hx
  dsimp
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv]
    change ‖(toEuclideanLin A) v‖ ≤ _
    calc ‖(toEuclideanLin A) v‖
      = ‖(toEuclideanLin A).toContinuousLinearMap v‖ := rfl
      _ ≤ ‖(toEuclideanLin A).toContinuousLinearMap‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖(toEuclideanLin A).toContinuousLinearMap‖ := by rw [hv, mul_one]
  · rw [ciSup_neg hv, Real.sSup_empty]; exact norm_nonneg _

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[opnorm_pos_def_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma opnorm_pos_def_norm
  {d : ℕ}
  [Nonempty (Fin d)]
  {A : Matrix (Fin d) (Fin d) ℝ}
-- given
  (hA : A.PosDef) :
-- imply
  matrixOpNorm A > 0 := by
-- proof
  obtain ⟨i⟩ := ‹Nonempty (Fin d)›
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
  have he_norm : ‖e‖ = 1 := by simp [e]
  have hdiag : 0 < A i i := hA.diag_pos
  have hAe_ne : A.mulVec (e : Fin d → ℝ) ≠ 0 := by
    intro h
    have := congr_fun h i
    simp [mulVec, dotProduct, e, EuclideanSpace.single] at this
    linarith
  have hAe_pos : 0 < ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec e)‖ := by
    rw [norm_pos_iff]
    intro h
    apply hAe_ne
    have := congr_arg (EuclideanSpace.equiv (Fin d) ℝ) h
    simp at this
    exact this
  calc matrixOpNorm A
    = ⨆ (v : EuclideanSpace ℝ (Fin d)) (_ : ‖v‖ = 1),
      ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖ := rfl
    _ ≥ ⨆ (_ : ‖e‖ = 1), ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec e)‖ :=
      le_ciSup_of_le (matrixOpNorm_bddAbove A) e le_rfl
    _ = ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec e)‖ := by
      rw [ciSup_pos he_norm]
    _ > 0 := hAe_pos

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[matrixOpNorm_eq_l2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma matrixOpNorm_eq_l2
  {d : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ} :
-- imply
  matrixOpNorm A = @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A := by
-- proof
  apply le_antisymm
  ·
    apply ciSup_le; intro v
    by_cases hv : ‖v‖ = 1
    · rw [ciSup_pos hv]; change ‖(toEuclideanLin A) v‖ ≤ _
      calc ‖(toEuclideanLin A) v‖ = ‖(toEuclideanLin A).toContinuousLinearMap v‖ := rfl
        _ ≤ ‖(toEuclideanLin A).toContinuousLinearMap‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖(toEuclideanLin A).toContinuousLinearMap‖ := by rw [hv, mul_one]
    · rw [ciSup_neg hv, Real.sSup_empty]; exact ContinuousLinearMap.opNorm_nonneg _
  ·
    show ‖(toEuclideanLin A).toContinuousLinearMap‖ ≤ _
    apply ContinuousLinearMap.opNorm_le_bound
    · apply Real.iSup_nonneg; intro v; apply Real.iSup_nonneg; intro _; exact norm_nonneg _
    · intro v
      change ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖ ≤ matrixOpNorm A * ‖v‖
      by_cases hv : v = 0
      · simp [hv, mulVec_zero]
      · have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
        let w : EuclideanSpace ℝ (Fin d) := (‖v‖⁻¹ : ℝ) • v
        have hw_norm : ‖w‖ = 1 := by simp [w, norm_smul, inv_mul_cancel₀ (ne_of_gt hv_pos)]
        have hAw : ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec w)‖ ≤ matrixOpNorm A := by
          calc ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec w)‖
            = ⨆ (_ : ‖w‖ = 1), ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec w)‖ := by
              rw [ciSup_pos hw_norm]
            _ ≤ _ := le_ciSup (matrixOpNorm_bddAbove A) w
        have hmv : A.mulVec w = ‖v‖⁻¹ • A.mulVec v := by simp [w, mulVec_smul]
        rw [hmv] at hAw
        simp only [map_smul, norm_smul, norm_inv, Real.norm_of_nonneg (le_of_lt hv_pos)] at hAw
        calc ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖
          = ‖v‖ * (‖v‖⁻¹ * ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖) := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hv_pos), one_mul]
          _ ≤ ‖v‖ * matrixOpNorm A := mul_le_mul_of_nonneg_left hAw (le_of_lt hv_pos)
          _ = matrixOpNorm A * ‖v‖ := mul_comm _ _

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[opnorm_whitening_bound_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma opnorm_whitening_bound_axiom
  {d : ℕ}
  {S covMat A : Matrix (Fin d) (Fin d) ℝ}
-- given
  (hWhiten : S * covMat * S.transpose = 1)
  (hPD : covMat.PosDef) :
-- imply
  matrixOpNorm A ≤ matrixOpNorm covMat * matrixOpNorm (S * A * S.transpose) := by
-- proof
  open scoped Matrix.Norms.L2Operator in
  rw [matrixOpNorm_eq_l2, matrixOpNorm_eq_l2, matrixOpNorm_eq_l2]
  have hSdet_ne : S.det ≠ 0 := by
    intro h
    have : (S * covMat * S.transpose).det = (1 : Matrix (Fin d) (Fin d) ℝ).det := by rw [hWhiten]
    simp [det_mul, det_transpose, h] at this
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet_ne
  have hSTdet : IsUnit S.transpose.det := by rwa [det_transpose]
  have hcov_eq : covMat = S⁻¹ * S.transpose⁻¹ := by
    have h2 : covMat * S.transpose = S⁻¹ := by
      have := congr_arg (S⁻¹ * ·) hWhiten
      simp only [mul_assoc] at this
      rw [← mul_assoc S⁻¹ S, nonsing_inv_mul _ hSdet, one_mul, mul_one] at this; exact this
    calc covMat = covMat * (S.transpose * S.transpose⁻¹) := by
      rw [mul_nonsing_inv _ hSTdet, mul_one]
      _ = covMat * S.transpose * S.transpose⁻¹ := by rw [← mul_assoc]
      _ = S⁻¹ * S.transpose⁻¹ := by rw [h2]
  have hA_eq : A = S⁻¹ * (S * A * S.transpose) * S.transpose⁻¹ := by
    simp only [mul_assoc]
    rw [mul_nonsing_inv _ hSTdet, mul_one, ← mul_assoc, nonsing_inv_mul _ hSdet, one_mul]
  have hST_inv : S.transpose⁻¹ = S⁻¹ᵀ := (transpose_nonsing_inv S).symm
  have h_transpose_norm : @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ᵀ =
    @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact l2_opNorm_conjTranspose _
  have hcov_norm : @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm covMat =
    @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ *
    @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ := by
    rw [hcov_eq, hST_inv]
    rw [← conjTranspose_eq_transpose_of_trivial S⁻¹]
    have h := l2_opNorm_conjTranspose_mul_self S⁻¹ᴴ
    rw [conjTranspose_conjTranspose] at h
    rw [l2_opNorm_conjTranspose] at h; exact h
  calc @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A
    = @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
      (S⁻¹ * (S * A * S.transpose) * S.transpose⁻¹) := by rw [← hA_eq]
    _ ≤ @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (S⁻¹ * (S * A * S.transpose)) *
      @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S.transpose⁻¹ := l2_opNorm_mul _ _
    _ ≤ (@norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ *
      @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (S * A * S.transpose)) *
      @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S.transpose⁻¹ := by
      apply mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
      exact @norm_nonneg _ Matrix.instL2OpNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup _
    _ = @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ *
      @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ *
      @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (S * A * S.transpose) := by
      rw [hST_inv, h_transpose_norm]; ring
    _ = @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm covMat *
      @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (S * A * S.transpose) := by
      rw [← hcov_norm]

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[opnorm_whitening_transfer_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma opnorm_whitening_transfer_axiom
  {d : ℕ}
  [Nonempty (Fin d)]
  {S covMat A : Matrix (Fin d) (Fin d) ℝ}
  {t : ℝ}
-- given
  (hWhiten : S * covMat * S.transpose = 1)
  (hPD : covMat.PosDef)
  (h : matrixOpNorm A > matrixOpNorm covMat * t) :
-- imply
  matrixOpNorm (S * A * S.transpose) > t := by
-- proof
  by_contra hle
  push Not at hle
  have hcov_pos : matrixOpNorm covMat > 0 := opnorm_pos_def_norm covMat hPD
  have hcov_nn : (0 : ℝ) ≤ matrixOpNorm covMat := le_of_lt hcov_pos
  have h2 : matrixOpNorm covMat * matrixOpNorm (S * A * S.transpose) ≤
    matrixOpNorm covMat * t :=
    mul_le_mul_of_nonneg_left hle hcov_nn
  have h3 : matrixOpNorm A ≤ matrixOpNorm covMat * matrixOpNorm (S * A * S.transpose) :=
    opnorm_whitening_bound_axiom S covMat A hWhiten hPD
  linarith

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[subgaussian_integrable_products](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma subgaussian_integrable_products
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → Fin d → ℝ}
  {σsq : ℝ}
  {j k : Fin d}
-- given
  (hSG : IsSubGaussianVec μ X σsq) :
-- imply
  Integrable (fun ω => X ω j * X ω k) μ := by
-- proof
  have hASM : ∀ i : Fin d, AEStronglyMeasurable (fun ω => X ω i) μ :=
    fun i => ((measurable_pi_apply i).comp_aemeasurable hSG.1).aestronglyMeasurable
  have hComp_lint : ∀ i : Fin d, ∀ s : ℝ,
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω i)) ∂μ ≤
      ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)) := by
    intro i s
    have hei : ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      rw [PiLp.norm_single]; simp
    have := hSG.2.2 (EuclideanSpace.single i 1) hei s
    simp at this; exact this
  set b := |σsq| + 1
  have hb_sq : σsq ≤ b ^ 2 := by
    calc σsq ≤ |σsq| := le_abs_self σsq
    _ ≤ |σsq| + 1 := le_add_of_nonneg_right (by positivity)
    _ ≤ (|σsq| + 1) ^ 2 := by nlinarith [abs_nonneg σsq]
  have hComp_b : ∀ i : Fin d, ∀ s : ℝ,
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω i)) ∂μ ≤
      ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)) := by
    intro i s
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω i)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)) := hComp_lint i s
      _ ≤ ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp_of_le; gcongr
  have hExpInt : ∀ i : Fin d, ∀ s : ℝ,
    Integrable (fun ω => Real.exp (s * X ω i)) μ := by
    intro i s
    exact exp_individual_integrable μ d (fun i ω => X ω i) b hComp_b hASM i s
  have hMemLp : ∀ i : Fin d, MemLp (fun ω => X ω i) 2 μ := by
    intro i
    rw [memLp_two_iff_integrable_sq (hASM i)]
    have hexp_pos := hExpInt i 1
    have hexp_neg := hExpInt i (-1)
    have h_abs_pow := ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul
      one_ne_zero hexp_pos hexp_neg 2
    convert h_abs_pow using 1; ext ω; rw [sq_abs]
  exact (hMemLp j).integrable_mul (hMemLp k)

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[of_eq_vecMulVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma of_eq_vecMulVec
  {d : ℕ}
  {v : Fin d → ℝ} :
-- imply
  Matrix.of (fun j k => v j * v k) = vecMulVec v v := by
-- proof
  ext j k; simp [vecMulVec_apply, of_apply]

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[outer_product_transform](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma outer_product_transform
  {d : ℕ}
  {S : Matrix (Fin d) (Fin d) ℝ}
  {v : Fin d → ℝ} :
-- imply
  S * vecMulVec v v * S.transpose = vecMulVec (S.mulVec v) (S.mulVec v) := by
-- proof
  rw [mul_vecMulVec, vecMulVec_mul]; congr 1
  rw [← mulVec_transpose]; simp [Matrix.transpose_transpose]

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[emp_cov_linear_transform](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma emp_cov_linear_transform
  {d : ℕ}
  {n : ℕ}
  {X : Fin n → Ω → Fin d → ℝ}
  {S : Matrix (Fin d) (Fin d) ℝ}
  {ω : Ω} :
-- imply
  empiricalCovariance (fun i ω => S.mulVec (X i ω)) ω = S * empiricalCovariance X ω * S.transpose := by
-- proof
  simp only [empiricalCovariance]
  rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [of_eq_vecMulVec, of_eq_vecMulVec, outer_product_transform]

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[integral_mulVec_eq_conjugated_cov](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma integral_mulVec_eq_conjugated_cov
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → Fin d → ℝ}
  {S covMat : Matrix (Fin d) (Fin d) ℝ}
  {j k : Fin d}
-- given
  (hcov : ∀ (j k : Fin d), ∫ ω, X ω j * X ω k ∂μ = covMat j k)
  (hSG : IsSubGaussianVec μ X (matrixOpNorm covMat)) :
-- imply
  ∫ ω, (S.mulVec (X ω)) j * (S.mulVec (X ω)) k ∂μ = (S * covMat * S.transpose) j k := by
-- proof
  simp only [mulVec, dotProduct]
  have hInt : ∀ (a b : Fin d), Integrable (fun ω => X ω a * X ω b) μ :=
    subgaussian_integrable_products μ X _ hSG
  conv_lhs => arg 2; ext ω; rw [Finset.sum_mul_sum]
  have hint_term : ∀ (c c' : Fin d),
    Integrable (fun ω => S j c * X ω c * (S k c' * X ω c')) μ := by
    intro c c'
    have : (fun ω => S j c * X ω c * (S k c' * X ω c')) =
      fun ω => (S j c * S k c') * (X ω c * X ω c') := by ext ω; ring
    rw [this]; exact (hInt c c').const_mul _
  rw [integral_finset_sum _ (fun c _ => integrable_finset_sum _ (fun c' _ => hint_term c c'))]
  simp_rw [integral_finset_sum _ (fun c' _ => hint_term _ c')]
  simp_rw [show ∀ (c c' : Fin d), (fun ω => S j c * X ω c * (S k c' * X ω c')) =
    (fun ω => (S j c * S k c') * (X ω c * X ω c')) from fun c c' => by ext ω; ring]
  simp_rw [integral_const_mul, hcov]
  simp only [mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro c' _
  ring

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[exp_16_ge_289](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma exp_16_ge_289
  {d : ℕ} :
-- imply
  (289 : ℝ) ≤ Real.exp 16 := by
-- proof
  have h : (0 : ℝ) ≤ 16 := by norm_num
  have := Real.sum_le_exp_of_nonneg h 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  norm_num at this
  linarith

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[h288_le_exp16](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma h288_le_exp16
  {d : ℕ} :
-- imply
  (288 : ℝ) ≤ Real.exp 16 :=
-- proof
  le_trans (by norm_num : (288 : ℝ) ≤ 289) exp_16_ge_289

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[h288d_le_exp16d](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma h288d_le_exp16d
  {d : ℕ}
  {d : ℕ} :
-- imply
  (288 : ℝ) ^ d ≤ Real.exp (16 * ↑d) := by
-- proof
  calc (288 : ℝ) ^ d ≤ (Real.exp 16) ^ d := by
    gcongr; exact h288_le_exp16
    _ = Real.exp (↑d * 16) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (16 * ↑d) := by ring_nf

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[exp_neg_log_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma exp_neg_log_bound
  {d : ℕ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hδ1 : δ < 1) :
-- imply
  Real.exp (-(16 * Real.log (1 / δ))) ≤ δ := by
-- proof
  rw [one_div, Real.log_inv, show -(16 * -Real.log δ) = ↑(16 : ℕ) * Real.log δ from by
    push_cast; ring]
  rw [Real.exp_nat_mul, Real.exp_log hδ]
  calc δ ^ 16 = δ ^ 1 * δ ^ 15 := by ring
    _ ≤ δ ^ 1 * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_one₀ (le_of_lt hδ) (le_of_lt hδ1)
      · exact pow_nonneg (le_of_lt hδ) 1
    _ = δ := by ring

end Rigollet.Chapter4.Thm_4_6

namespace Rigollet.Chapter4.Thm_4_6

/--
[rate_algebraic_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean)
-/
@[path]
lemma rate_algebraic_bound
  {d : ℕ}
  {n : ℕ}
  {δ : ℝ}
-- given
  (hd : 0 < d)
  (hn : 0 < n)
  (hδ : 0 < δ)
  (hδ1 : δ < 1) :
-- imply
  (288 : ℝ) ^ d * Real.exp (-(↑n / 2 * min ((1024 * covRate d n δ / 32) ^ 2) (1024 * covRate d n δ / 32))) ≤ δ := by
-- proof
  set r := (d : ℝ) + Real.log (1 / δ) with hr_def
  set c := covRate d n δ with hc_def
  have h_simp : 1024 * c / 32 = 32 * c := by ring
  rw [h_simp]
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hlog_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos; rw [one_div]; exact (one_lt_inv₀ hδ).mpr hδ1
  have hr_pos : 0 < r := by linarith
  have hc_ge_rn : c ≥ r / ↑n := by
    simp only [hc_def, covRate]; exact le_max_right _ _
  have hc_ge_sqrt : c ≥ Real.sqrt (r / ↑n) := by
    simp only [hc_def, covRate]; exact le_max_left _ _
  have hc_pos : 0 < c := by linarith [div_pos hr_pos hn_pos]
  have h_exp_bound : ↑n / 2 * min ((32 * c) ^ 2) (32 * c) ≥ 16 * r := by
    by_cases h : 1 ≤ 32 * c
    · have hsq : (32 * c) ^ 2 ≥ 32 * c := by nlinarith
      rw [min_eq_right hsq.le]
      have : ↑n / 2 * (32 * c) ≥ ↑n / 2 * (32 * (r / ↑n)) := by nlinarith
      linarith [show ↑n / 2 * (32 * (r / ↑n)) = 16 * r from by field_simp; ring]
    · push Not at h
      have hsq : (32 * c) ^ 2 ≤ 32 * c := by nlinarith
      rw [min_eq_left hsq]
      have hrn_nn : 0 ≤ r / ↑n := le_of_lt (div_pos hr_pos hn_pos)
      have hcsq : c ^ 2 ≥ r / ↑n := by
        have h1 : Real.sqrt (r / ↑n) ≤ c := hc_ge_sqrt
        have h2 : 0 ≤ Real.sqrt (r / ↑n) := Real.sqrt_nonneg _
        have h3 : (Real.sqrt (r / ↑n)) ^ 2 = r / ↑n := Real.sq_sqrt hrn_nn
        nlinarith [sq_nonneg (c - Real.sqrt (r / ↑n))]
      have : (32 * c) ^ 2 = 1024 * c ^ 2 := by ring
      rw [this]
      have h1 : ↑n / 2 * (1024 * (r / ↑n)) = 512 * r := by field_simp; ring
      nlinarith
  calc (288 : ℝ) ^ d * Real.exp (-(↑n / 2 * min ((32 * c) ^ 2) (32 * c)))
    ≤ Real.exp (16 * ↑d) * Real.exp (-(16 * r)) := by
      apply mul_le_mul (h288d_le_exp16d d) _ (le_of_lt (Real.exp_pos _))
        (le_of_lt (Real.exp_pos _))
      apply Real.exp_le_exp.mpr; linarith
    _ = Real.exp (-(16 * Real.log (1 / δ))) := by
      rw [← Real.exp_add]; congr 1; rw [hr_def]; ring
    _ ≤ δ := exp_neg_log_bound δ hδ hδ1
/-- **Theorem 4.6 (empirical covariance operator norm).** There is a universal constant `C > 0`
such that for `n` i.i.d. sub-Gaussian samples `X₁, …, Xₙ` with `E[X X^⊤] = Σ ≻ 0` and
`X ~ subG_d(‖Σ‖_op)`,
`‖Σ̂ - Σ‖_op ≤ C · ‖Σ‖_op · (√((d + log(1/δ))/n) ∨ (d + log(1/δ))/n)`
with probability at least `1 - δ`. -/
end Rigollet.Chapter4.Thm_4_6



-- created on 2026-10-23
