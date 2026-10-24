import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Prop_2_1
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter2.Prop_2_1
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_19
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_19
open Matrix Rigollet


namespace Rigollet.Chapter2

/--
[dotProduct_sub_expand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma dotProduct_sub_expand
  {n : ℕ}
  {a b : Fin n → ℝ} :
-- imply
  dotProduct (a - b) (a - b) = dotProduct a a - 2 * dotProduct a b + dotProduct b b := by
-- proof
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm b a]
  ring

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[dotProduct_eq_euclidean_norm_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma dotProduct_eq_euclidean_norm_sq
  {n : ℕ}
  {v : Fin n → ℝ} :
-- imply
  dotProduct v v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
-- proof
  have h := @EuclideanSpace.inner_toLp_toLp (Fin n) ℝ _ _ v v
  simp only [star_trivial] at h
  rwa [sq, ← @real_inner_self_eq_norm_mul_norm (EuclideanSpace ℝ (Fin n))]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[thm_2_2_fundamental_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma thm_2_2_fundamental_inequality
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Fin n → ℝ}
  {θhat : Fin d → ℝ}
-- given
  (hLS : ∀ θ : Fin d → ℝ, dotProduct ((X *ᵥ θstar + ε) - X *ᵥ θhat) ((X *ᵥ θstar + ε) - X *ᵥ θhat) ≤ dotProduct ((X *ᵥ θstar + ε) - X *ᵥ θ) ((X *ᵥ θstar + ε) - X *ᵥ θ)) :
-- imply
  dotProduct (X *ᵥ (θhat - θstar)) (X *ᵥ (θhat - θstar)) ≤ 2 * dotProduct ε (X *ᵥ (θhat - θstar)) := by
-- proof
  have h1 := hLS θstar
  have heps : (X *ᵥ θstar + ε) - X *ᵥ θstar = ε := by
    simp [add_sub_cancel_left]
  rw [heps] at h1
  set v := X *ᵥ (θhat - θstar) with hv_def
  have hresid : (X *ᵥ θstar + ε) - X *ᵥ θhat = ε - v := by
    rw [hv_def, mulVec_sub]; ext i; simp [Pi.sub_apply, Pi.add_apply]; ring
  rw [hresid] at h1
  rw [dotProduct_sub_expand] at h1
  linarith

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[subG_variance_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma subG_variance_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {Z : Ω → ℝ}
  {σ : ℝ}
-- given
  (hσ : 0 < σ)
  (hZ_int : MeasureTheory.Integrable Z μ)
  (hexp_int : ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * Z ω)) μ)
  (hsubG : ∀ s : ℝ, ∫ ω, Real.exp (s * Z ω) ∂μ ≤ Real.exp (s ^ 2 * σ ^ 2 / 2)) :
-- imply
  ∫ ω, (Z ω) ^ 2 ∂μ ≤ 4 * σ ^ 2 := by
-- proof
  open MeasureTheory in
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hσ_sq_pos : 0 < σ ^ 2 := by positivity
  have hint_pos : Integrable (fun ω => Real.exp (σ⁻¹ * Z ω)) μ := hexp_int σ⁻¹
  have hint_neg : Integrable (fun ω => Real.exp (-(σ⁻¹ * Z ω))) μ := by
    convert hexp_int (-σ⁻¹) using 1; ext ω; ring_nf
  have sq_le_cosh : ∀ (t : ℝ), t ^ 2 ≤ Real.exp t + Real.exp (-t) := by
    intro t
    have habs : 0 ≤ |t| := abs_nonneg _
    have hab : Real.exp t + Real.exp (-t) = Real.exp |t| + Real.exp (-|t|) := by
      cases le_or_gt 0 t with
      | inl h => rw [abs_of_nonneg h]
      | inr h => rw [abs_of_neg h]; ring_nf
    rw [hab, (sq_abs t).symm]
    have h4 := Real.sum_le_exp_of_nonneg habs 4
    have hsum : ∑ i ∈ Finset.range 4, |t| ^ i / ↑i.factorial =
      1 + |t| + |t| ^ 2 / 2 + |t| ^ 3 / 6 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.factorial, pow_zero, pow_one, Nat.cast_one, div_one]
      push_cast; ring
    rw [hsum] at h4
    nlinarith [Real.exp_pos (-|t|), sq_nonneg (|t| - 3/2),
      mul_nonneg habs (sq_nonneg (|t| - 3/2))]
  have hpw : ∀ ω, (Z ω) ^ 2 ≤ σ ^ 2 * (Real.exp (σ⁻¹ * Z ω) + Real.exp (-(σ⁻¹ * Z ω))) := by
    intro ω
    have h := sq_le_cosh (σ⁻¹ * Z ω)
    have hsq : (σ⁻¹ * Z ω) ^ 2 = (Z ω) ^ 2 / σ ^ 2 := by
      rw [mul_pow, inv_pow, inv_mul_eq_div]
    rw [hsq] at h
    linarith [(div_le_iff₀ hσ_sq_pos).mp h]
  have hdom_int : Integrable (fun ω => σ ^ 2 * (Real.exp (σ⁻¹ * Z ω) + Real.exp (-(σ⁻¹ * Z ω)))) μ :=
    (hint_pos.add hint_neg).const_mul _
  have hZ2_int : Integrable (fun ω => (Z ω) ^ 2) μ := by
    refine hdom_int.mono (hZ_int.aestronglyMeasurable.pow 2) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [Real.norm_of_nonneg (by nlinarith [Real.exp_pos (σ⁻¹ * Z ω), Real.exp_pos (-(σ⁻¹ * Z ω))])]
    exact hpw ω
  calc ∫ ω, (Z ω) ^ 2 ∂μ
    ≤ ∫ ω, σ ^ 2 * (Real.exp (σ⁻¹ * Z ω) + Real.exp (-(σ⁻¹ * Z ω))) ∂μ :=
      integral_mono hZ2_int hdom_int hpw
    _ = σ ^ 2 * ∫ ω, (Real.exp (σ⁻¹ * Z ω) + Real.exp (-(σ⁻¹ * Z ω))) ∂μ :=
      integral_const_mul _ _
    _ = σ ^ 2 * (∫ ω, Real.exp (σ⁻¹ * Z ω) ∂μ + ∫ ω, Real.exp (-(σ⁻¹ * Z ω)) ∂μ) := by
      congr 1; exact integral_add hint_pos hint_neg
    _ ≤ σ ^ 2 * (Real.exp (σ⁻¹ ^ 2 * σ ^ 2 / 2) + Real.exp ((-σ⁻¹) ^ 2 * σ ^ 2 / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hσ_sq_pos)
      apply add_le_add
      · exact hsubG σ⁻¹
      · convert hsubG (-σ⁻¹) using 1; congr 1; ext ω; ring_nf
    _ = σ ^ 2 * (Real.exp (1/2) + Real.exp (1/2)) := by
      congr 1
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hσ_ne),
        neg_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hσ_ne)]
    _ = σ ^ 2 * (2 * Real.exp (1/2)) := by ring
    _ ≤ σ ^ 2 * (2 * 2) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hσ_sq_pos)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have key : Real.exp (1 : ℝ) < 4 := by
        have := Real.exp_one_lt_d9; linarith
      have mul_eq : Real.exp (1/2 : ℝ) * Real.exp (1/2 : ℝ) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1/2 : ℝ), sq_nonneg (Real.exp (1/2 : ℝ) - 2)]
    _ = 4 * σ ^ 2 := by ring

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[inner_toLp_toLp_eq_dotProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma inner_toLp_toLp_eq_dotProduct
  {n : ℕ}
  {u v : Fin n → ℝ} :
-- imply
  @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (WithLp.toLp (p := 2) u) (WithLp.toLp (p := 2) v) = dotProduct u v := by
-- proof
  simp [dotProduct, inner]; congr 1; ext i; ring
set_option maxHeartbeats 800000 in

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[exists_onb_with_parseval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma exists_onb_with_parseval
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {r : ℕ}
-- given
  (hr : r = (X.transpose * X).rank) :
-- imply
  ∃ (Φ : Fin r → (Fin n → ℝ)), (∀ i : Fin r, dotProduct (Φ i) (Φ i) = 1) ∧ (∀ i j : Fin r, i ≠ j → dotProduct (Φ i) (Φ j) = 0) ∧ (∀ (δ : Fin d → ℝ), dotProduct (X *ᵥ δ) (X *ᵥ δ) = ∑ i : Fin r, (dotProduct (X *ᵥ δ) (Φ i)) ^ 2) ∧ (∀ (w : Fin n → ℝ) (δ : Fin d → ℝ), dotProduct w (X *ᵥ δ) = ∑ i : Fin r, dotProduct (X *ᵥ δ) (Φ i) * dotProduct w (Φ i)) := by
-- proof
  set U : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (X.mulVecLin).range.map (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap with hU_def
  have hfr : Module.finrank ℝ U = r := by
    rw [hr, Matrix.rank_transpose_mul_self, LinearEquiv.finrank_map_eq]; rfl
  set b := (stdOrthonormalBasis ℝ U).reindex (finCongr hfr)
  set Φ : Fin r → (Fin n → ℝ) := fun i => (WithLp.equiv 2 (Fin n → ℝ)) (b i).1
  have hΦi_eq : ∀ i, (b i).1 = WithLp.toLp (p := 2) (Φ i) := fun i => by simp [Φ]
  have hv_mem : ∀ δ : Fin d → ℝ, WithLp.toLp (p := 2) (X *ᵥ δ) ∈ U := by
    intro δ; rw [hU_def]
    exact Submodule.mem_map.mpr ⟨X *ᵥ δ, LinearMap.mem_range.mpr ⟨δ, rfl⟩, by simp⟩
  have expansion : ∀ (v_U : ↥U),
    (v_U : EuclideanSpace ℝ (Fin n)) =
      ∑ i : Fin r, @inner ℝ ↥U _ (b i) v_U • ((b i) : EuclideanSpace ℝ (Fin n)) := by
    intro v_U
    have h := b.sum_repr v_U
    apply_fun (↑· : U → EuclideanSpace ℝ (Fin n)) at h
    rw [Submodule.coe_sum] at h; simp_rw [SetLike.val_smul] at h; rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [b.repr_apply_apply]
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  ·
    intro i
    have : dotProduct (Φ i) (Φ i) = @inner ℝ ↥U _ (b i) (b i) := by
      rw [← inner_toLp_toLp_eq_dotProduct, ← hΦi_eq, ← Submodule.coe_inner]
    rw [this, real_inner_self_eq_norm_sq, b.orthonormal.1 i]; norm_num
  ·
    intro i j hij
    have : dotProduct (Φ i) (Φ j) = @inner ℝ ↥U _ (b i) (b j) := by
      rw [← inner_toLp_toLp_eq_dotProduct, ← hΦi_eq, ← hΦi_eq, ← Submodule.coe_inner]
    rw [this, b.orthonormal.2 hij]
  ·
    intro δ
    set v_U : ↥U := ⟨WithLp.toLp (p := 2) (X *ᵥ δ), hv_mem δ⟩
    calc dotProduct (X *ᵥ δ) (X *ᵥ δ)
      = @inner ℝ ↥U _ v_U v_U := by
        rw [Submodule.coe_inner]; exact (inner_toLp_toLp_eq_dotProduct _ _).symm
      _ = ∑ i, @inner ℝ ↥U _ v_U (b i) * @inner ℝ ↥U _ (b i) v_U := by
        rw [← b.sum_inner_mul_inner v_U v_U]
      _ = ∑ i, (dotProduct (X *ᵥ δ) (Φ i)) ^ 2 := by
        congr 1; ext i
        rw [Submodule.coe_inner, Submodule.coe_inner, hΦi_eq,
          inner_toLp_toLp_eq_dotProduct, inner_toLp_toLp_eq_dotProduct,
          dotProduct_comm (Φ i)]; ring
  ·
    intro w δ
    set v_U : ↥U := ⟨WithLp.toLp (p := 2) (X *ᵥ δ), hv_mem δ⟩
    calc dotProduct w (X *ᵥ δ)
      = @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (WithLp.toLp (p := 2) w) v_U.1 :=
        (inner_toLp_toLp_eq_dotProduct _ _).symm
      _ = @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (WithLp.toLp (p := 2) w)
        (∑ i, @inner ℝ ↥U _ (b i) v_U • ((b i) : EuclideanSpace ℝ (Fin n))) := by
        rw [expansion v_U]
      _ = ∑ i, dotProduct (X *ᵥ δ) (Φ i) * dotProduct w (Φ i) := by
        rw [inner_sum]; simp_rw [inner_smul_right]
        congr 1; ext i
        rw [Submodule.coe_inner, hΦi_eq,
          inner_toLp_toLp_eq_dotProduct, inner_toLp_toLp_eq_dotProduct,
          dotProduct_comm (Φ i)]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[integrable_of_mgf_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma integrable_of_mgf_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {Z : Ω → ℝ}
  {σ : ℝ}
-- given
  (_hmgf : ∀ s : ℝ, ∫ ω, Real.exp (s * Z ω) ∂μ ≤ Real.exp (s ^ 2 * σ ^ 2 / 2))
  (hint : ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * Z ω)) μ) :
-- imply
  MeasureTheory.Integrable Z μ ∧ (∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * Z ω)) μ) ∧ MeasureTheory.Integrable (fun ω => (Z ω) ^ 2) μ := by
-- proof
  open MeasureTheory in
  refine ⟨?_, hint, ?_⟩
  · have hZ_asm : AEStronglyMeasurable Z μ := by
    have h1 := (hint 1).aestronglyMeasurable
    have hae : AEMeasurable Z μ := by
      have h1m := h1.aemeasurable
      have h2 : AEMeasurable (fun ω => 1 * Z ω) μ := by
        have : (fun ω => 1 * Z ω) = fun ω => Real.log (Real.exp (1 * Z ω)) := by
          ext ω; simp [Real.log_exp]
        rw [this]; exact h1m.log
      simpa using h2
    exact hae.aestronglyMeasurable
    have hint_pos := hint 1
    have hint_neg : Integrable (fun ω => Real.exp (-(1 * Z ω))) μ := by
      convert hint (-1) using 1; ext ω; ring_nf
    refine (hint_pos.add hint_neg).mono hZ_asm ?_
    filter_upwards with ω
    simp only [Real.norm_eq_abs, one_mul, Pi.add_apply]
    have h1 : 0 < Real.exp (Z ω) + Real.exp (-Z ω) := by positivity
    rw [abs_of_pos h1]
    rw [abs_le]
    constructor
    · linarith [Real.add_one_le_exp (-Z ω), Real.exp_pos (Z ω)]
    · linarith [Real.add_one_le_exp (Z ω), Real.exp_pos (-Z ω)]
  ·
    have hZ_int : Integrable Z μ := by
      have hZ_asm : AEStronglyMeasurable Z μ := by
        have h1 := (hint 1).aestronglyMeasurable
        have hae : AEMeasurable Z μ := by
          have h1m := h1.aemeasurable
          have h2 : AEMeasurable (fun ω => 1 * Z ω) μ := by
            have : (fun ω => 1 * Z ω) = fun ω => Real.log (Real.exp (1 * Z ω)) := by
              ext ω; simp [Real.log_exp]
            rw [this]; exact h1m.log
          simpa using h2
        exact hae.aestronglyMeasurable
      have hint_pos := hint 1
      have hint_neg : Integrable (fun ω => Real.exp (-(1 * Z ω))) μ := by
        convert hint (-1) using 1; ext ω; ring_nf
      refine (hint_pos.add hint_neg).mono hZ_asm ?_
      filter_upwards with ω
      simp only [Real.norm_eq_abs, one_mul, Pi.add_apply]
      have h1 : 0 < Real.exp (Z ω) + Real.exp (-Z ω) := by positivity
      rw [abs_of_pos h1]
      rw [abs_le]
      constructor
      · linarith [Real.add_one_le_exp (-Z ω), Real.exp_pos (Z ω)]
      · linarith [Real.add_one_le_exp (Z ω), Real.exp_pos (-Z ω)]
    have hZ_asm := hZ_int.aestronglyMeasurable
    have hint_pos := hint 1
    have hint_neg : Integrable (fun ω => Real.exp (-(1 * Z ω))) μ := by
      convert hint (-1) using 1; ext ω; ring_nf
    have hdom : Integrable (fun ω => Real.exp (1 * Z ω) + Real.exp (-(1 * Z ω))) μ :=
      hint_pos.add hint_neg
    refine hdom.mono (hZ_asm.pow 2) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [one_mul]
    rw [Real.norm_of_nonneg (by positivity)]
    have habs : 0 ≤ |Z ω| := abs_nonneg _
    rw [(sq_abs (Z ω)).symm]
    have h4 := Real.sum_le_exp_of_nonneg habs 4
    have hsum : ∑ i ∈ Finset.range 4, |Z ω| ^ i / ↑i.factorial =
      1 + |Z ω| + |Z ω| ^ 2 / 2 + |Z ω| ^ 3 / 6 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.factorial, pow_zero, pow_one, Nat.cast_one, div_one]
      push_cast; ring
    rw [hsum] at h4
    have hab : Real.exp (Z ω) + Real.exp (-(Z ω)) = Real.exp |Z ω| + Real.exp (-|Z ω|) := by
      cases le_or_gt 0 (Z ω) with
      | inl h => rw [abs_of_nonneg h]
      | inr h => rw [abs_of_neg h]; ring_nf
    rw [hab]
    nlinarith [Real.exp_pos (-|Z ω|), sq_nonneg (|Z ω| - 3/2),
      mul_nonneg habs (sq_nonneg (|Z ω| - 3/2))]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[exists_onb_pointwise_bound_with_integrability](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma exists_onb_pointwise_bound_with_integrability
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {ε : Ω → Fin n → ℝ}
  {r : ℕ}
  {σ : ℝ}
-- given
  (hr : r = (X.transpose * X).rank)
  (_hσ : 0 < σ)
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤ Real.exp (s ^ 2 * σ ^ 2 / 2))
  (hsubG_int : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ) :
-- imply
  ∃ (Φ : Fin r → (Fin n → ℝ)), (∀ i : Fin r, dotProduct (Φ i) (Φ i) = 1) ∧ (∀ (δ : Fin d → ℝ) (v : Fin n → ℝ), dotProduct (X *ᵥ δ) (X *ᵥ δ) ≤ 2 * dotProduct v (X *ᵥ δ) → dotProduct (X *ᵥ δ) (X *ᵥ δ) ≤ 4 * ∑ i : Fin r, (dotProduct v (Φ i)) ^ 2) ∧ (∀ i : Fin r, MeasureTheory.Integrable (fun ω => dotProduct (ε ω) (Φ i)) μ) ∧ (∀ i : Fin r, ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) (Φ i))) μ) ∧ (∀ i : Fin r, MeasureTheory.Integrable (fun ω => (dotProduct (ε ω) (Φ i)) ^ 2) μ) := by
-- proof
  obtain ⟨Φ, hunit, _, hparseval, hexpand⟩ := exists_onb_with_parseval X r hr
  refine ⟨Φ, hunit, ?_, ?_, ?_, ?_⟩
  ·
    intro δ v hfund
    rw [hexpand v δ] at hfund
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => dotProduct (X *ᵥ δ) (Φ i)) (fun i => dotProduct v (Φ i))
    set P := ∑ i : Fin r, (dotProduct (X *ᵥ δ) (Φ i)) ^ 2
    set S := ∑ i : Fin r, (dotProduct v (Φ i)) ^ 2
    set T := ∑ i : Fin r, dotProduct (X *ᵥ δ) (Φ i) * dotProduct v (Φ i)
    rw [hparseval δ] at hfund ⊢
    nlinarith [sq_nonneg T, sq_nonneg P,
      Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (dotProduct (X *ᵥ δ) (Φ i))),
      Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (dotProduct v (Φ i)))]
  ·
    intro i
    have hi_unit : dotProduct (Φ i) (Φ i) ≤ 1 := le_of_eq (hunit i)
    exact (integrable_of_mgf_bound (fun ω => dotProduct (ε ω) (Φ i)) σ
      (hsubG (Φ i) hi_unit) (hsubG_int (Φ i) hi_unit)).1
  ·
    intro i s
    have hi_unit : dotProduct (Φ i) (Φ i) ≤ 1 := le_of_eq (hunit i)
    exact (integrable_of_mgf_bound (fun ω => dotProduct (ε ω) (Φ i)) σ
      (hsubG (Φ i) hi_unit) (hsubG_int (Φ i) hi_unit)).2.1 s
  ·
    intro i
    have hi_unit : dotProduct (Φ i) (Φ i) ≤ 1 := le_of_eq (hunit i)
    exact (integrable_of_mgf_bound (fun ω => dotProduct (ε ω) (Φ i)) σ
      (hsubG (Φ i) hi_unit) (hsubG_int (Φ i) hi_unit)).2.2

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[sup_out_onb_expectation_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma sup_out_onb_expectation_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {θhat : Ω → Fin d → ℝ}
  {σ : ℝ}
  {r : ℕ}
-- given
  (hσ : 0 < σ)
  (hr : r = (X.transpose * X).rank)
  (hfund : ∀ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤ 2 * dotProduct (ε ω) (X *ᵥ (θhat ω - θstar)))
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤ Real.exp (s ^ 2 * σ ^ 2 / 2))
  (hsubG_int : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ)
  (hvar : ∀ (Z : Ω → ℝ), MeasureTheory.Integrable Z μ → (∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * Z ω)) μ) → (∀ s : ℝ, ∫ ω, Real.exp (s * Z ω) ∂μ ≤ Real.exp (s ^ 2 * σ ^ 2 / 2)) → ∫ ω, (Z ω) ^ 2 ∂μ ≤ 4 * σ ^ 2) :
-- imply
  ∫ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ∂μ ≤ 16 * σ ^ 2 * ↑r := by
-- proof
  obtain ⟨Φ, hΦ_unit, hΦ_bound, hΦ_int, hΦ_exp_int, hΦ_sq_int⟩ :=
    exists_onb_pointwise_bound_with_integrability X ε r hr σ hσ hsubG hsubG_int
  have hpw : ∀ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤
    4 * ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 :=
    fun ω => hΦ_bound (θhat ω - θstar) (ε ω) (hfund ω)
  have hvar_i : ∀ i : Fin r, ∫ ω, (dotProduct (ε ω) (Φ i)) ^ 2 ∂μ ≤ 4 * σ ^ 2 := by
    intro i
    exact hvar (fun ω => dotProduct (ε ω) (Φ i)) (hΦ_int i) (hΦ_exp_int i)
      (fun s => hsubG (Φ i) (le_of_eq (hΦ_unit i)) s)
  have hsum_bound : ∑ i : Fin r, ∫ ω, (dotProduct (ε ω) (Φ i)) ^ 2 ∂μ ≤
    ↑r * (4 * σ ^ 2) := by
    calc ∑ i : Fin r, ∫ ω, (dotProduct (ε ω) (Φ i)) ^ 2 ∂μ
      ≤ ∑ _i : Fin r, (4 * σ ^ 2) :=
        Finset.sum_le_sum (fun i _ => hvar_i i)
      _ = ↑r * (4 * σ ^ 2) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hsum_int : MeasureTheory.Integrable
    (fun ω => 4 * ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2) μ :=
    (MeasureTheory.integrable_finset_sum _ (fun i _ => hΦ_sq_int i)).const_mul _
  calc ∫ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ∂μ
    ≤ ∫ ω, 4 * ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 ∂μ := by
      apply MeasureTheory.integral_mono_of_nonneg
      · filter_upwards with ω
        have : star (X *ᵥ (θhat ω - θstar)) = X *ᵥ (θhat ω - θstar) := by
          simp [star_trivial]
        rw [← this]
        exact dotProduct_star_self_nonneg _
      · exact hsum_int
      · filter_upwards with ω; exact hpw ω
    _ = 4 * ∫ ω, ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 ∂μ :=
      MeasureTheory.integral_const_mul _ _
    _ = 4 * ∑ i : Fin r, ∫ ω, (dotProduct (ε ω) (Φ i)) ^ 2 ∂μ := by
      congr 1
      exact MeasureTheory.integral_finset_sum _ (fun i _ => hΦ_sq_int i)
    _ ≤ 4 * (↑r * (4 * σ ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum_bound (by norm_num)
    _ = 16 * σ ^ 2 * ↑r := by ring

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[subG_zero_dot_product_ae_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma subG_zero_dot_product_ae_zero
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {n : ℕ}
  {ε : Ω → Fin n → ℝ}
  {v : Fin n → ℝ}
-- given
  (_hv : dotProduct v v ≤ 1)
  (hsubG : ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤ Real.exp (s ^ 2 * 0 ^ 2 / 2))
  (hsubG_int : ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ) :
-- imply
  ∀ᵐ ω ∂μ, dotProduct (ε ω) v = 0 := by
-- proof
  have hsubG' : ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤ 1 := by
    intro s; have := hsubG s
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_zero, zero_div, Real.exp_zero] at this; exact this
  set Z := fun ω => dotProduct (ε ω) v with hZ_def
  obtain ⟨_, hZ_exp_int, hZ_sq_int⟩ := integrable_of_mgf_bound Z 0 hsubG hsubG_int
  have hbound : ∀ s : ℝ, 0 < s → s ^ 2 * ∫ ω, (Z ω) ^ 2 ∂μ ≤ 2 := by
    intro s hs
    have hpw' : ∀ ω, s ^ 2 * (Z ω) ^ 2 ≤
      Real.exp (s * Z ω) + Real.exp (-(s * Z ω)) := by
      intro ω; rw [← mul_pow]
      have habs : 0 ≤ |s * Z ω| := abs_nonneg _
      have hab : Real.exp (s * Z ω) + Real.exp (-(s * Z ω)) =
        Real.exp |s * Z ω| + Real.exp (-|s * Z ω|) := by
        cases le_or_gt 0 (s * Z ω) with
        | inl h => rw [abs_of_nonneg h]
        | inr h => rw [abs_of_neg h]; ring_nf
      rw [hab, (sq_abs (s * Z ω)).symm]
      have h4 := Real.sum_le_exp_of_nonneg habs 4
      have hsum : ∑ i ∈ Finset.range 4, |s * Z ω| ^ i / ↑i.factorial =
        1 + |s * Z ω| + |s * Z ω| ^ 2 / 2 + |s * Z ω| ^ 3 / 6 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          Nat.factorial, pow_zero, pow_one, Nat.cast_one, div_one]
        push_cast; ring
      rw [hsum] at h4
      nlinarith [Real.exp_pos (-|s * Z ω|), sq_nonneg (|s * Z ω| - 3/2),
        mul_nonneg habs (sq_nonneg (|s * Z ω| - 3/2))]
    have hint_neg : MeasureTheory.Integrable
      (fun ω => Real.exp (-(s * Z ω))) μ := by
      have h := hZ_exp_int (-s)
      simp only [hZ_def] at h ⊢
      convert h using 1; ext ω; ring_nf
    calc s ^ 2 * ∫ ω, (Z ω) ^ 2 ∂μ
      = ∫ ω, s ^ 2 * (Z ω) ^ 2 ∂μ :=
        (MeasureTheory.integral_const_mul _ _).symm
      _ ≤ ∫ ω, (Real.exp (s * Z ω) + Real.exp (-(s * Z ω))) ∂μ :=
        MeasureTheory.integral_mono (hZ_sq_int.const_mul _)
          ((hZ_exp_int s).add hint_neg) hpw'
      _ = ∫ ω, Real.exp (s * Z ω) ∂μ +
        ∫ ω, Real.exp (-(s * Z ω)) ∂μ :=
        MeasureTheory.integral_add (hZ_exp_int s) hint_neg
      _ ≤ 1 + 1 := by
        apply add_le_add (hsubG' s)
        simp only [hZ_def]
        convert hsubG' (-s) using 1; congr 1; ext ω; ring_nf
      _ = 2 := by ring
  have hZ_sq_nonneg_ae : 0 ≤ᵐ[μ] (fun ω => (Z ω) ^ 2) :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hZ_sq_int_nonneg : 0 ≤ ∫ ω, (Z ω) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg_of_ae hZ_sq_nonneg_ae
  have hZ_sq_le_zero : ∫ ω, (Z ω) ^ 2 ∂μ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hpos' : 0 < ∫ ω, (Z ω) ^ 2 ∂μ :=
      lt_of_le_of_ne hZ_sq_int_nonneg (Ne.symm (ne_of_gt hpos))
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ∫ ω, (Z ω) ^ 2 ∂μ)
    have hN_pos_real : (0 : ℝ) < N := lt_trans (by positivity) hN
    have hN_pos : 0 < N := by exact_mod_cast hN_pos_real
    have h1 := hbound N (by exact_mod_cast hN_pos)
    have h2 : 2 < ↑N * ∫ ω, (Z ω) ^ 2 ∂μ := by rwa [div_lt_iff₀ hpos'] at hN
    nlinarith [sq_nonneg (N : ℝ), (show (1 : ℝ) ≤ N by exact_mod_cast hN_pos)]
  have hZ_sq_eq_zero : ∫ ω, (Z ω) ^ 2 ∂μ = 0 :=
    le_antisymm hZ_sq_le_zero hZ_sq_int_nonneg
  have hZ_sq_ae_zero : ∀ᵐ ω ∂μ, (Z ω) ^ 2 = 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hZ_sq_nonneg_ae hZ_sq_int).mp
      hZ_sq_eq_zero
  filter_upwards [hZ_sq_ae_zero] with ω hω
  exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hω

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[subG_zero_sigma_integral_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma subG_zero_sigma_integral_le_zero
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {θhat : Ω → Fin d → ℝ}
-- given
  (hfund : ∀ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤ 2 * dotProduct (ε ω) (X *ᵥ (θhat ω - θstar)))
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤ Real.exp (s ^ 2 * 0 ^ 2 / 2))
  (hsubG_int : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ) :
-- imply
  ∫ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ∂μ ≤ 0 := by
-- proof
  have hε_ae : ∀ᵐ ω ∂μ, ε ω = 0 := by
    have hcomp : ∀ i : Fin n, ∀ᵐ ω ∂μ, ε ω i = 0 := by
      intro i
      have hei : dotProduct (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) ≤ 1 := by
        simp [dotProduct, Pi.single, Function.update]
      have hae := subG_zero_dot_product_ae_zero ε (Pi.single i 1) hei (hsubG _ hei) (hsubG_int _ hei)
      filter_upwards [hae] with ω hω
      have : dotProduct (ε ω) (Pi.single i 1) = ε ω i := by
        simp [dotProduct, Pi.single, Function.update]
      rwa [this] at hω
    have hall : ∀ᵐ ω ∂μ, ∀ i : Fin n, ε ω i = 0 :=
      (Filter.eventually_all (p := fun i ω => ε ω i = 0)).mpr hcomp
    filter_upwards [hall] with ω hω
    funext i; exact hω i
  have hf_ae : (fun ω => dotProduct (X *ᵥ (θhat ω - θstar))
    (X *ᵥ (θhat ω - θstar))) ≤ᵐ[μ] 0 := by
    filter_upwards [hε_ae] with ω hω
    have h := hfund ω
    have hzero : dotProduct (ε ω) (X *ᵥ (θhat ω - θstar)) = 0 := by
      rw [hω]; simp [dotProduct]
    simp only [Pi.zero_apply]
    linarith
  exact MeasureTheory.integral_nonpos_of_ae hf_ae

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[subG_expected_squared_norm_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma subG_expected_squared_norm_bound
  {_ : MeasurableSpace Ω}
  {μ : MeasureTheory.Measure Ω}
  {_ : MeasureTheory.IsProbabilityMeasure μ}
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {θhat : Ω → Fin d → ℝ}
  {σ : ℝ}
  {r : ℕ}
-- given
  (hr : r = (X.transpose * X).rank)
  (hLS : ∀ ω, ∀ θ : Fin d → ℝ, dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ (θhat ω)) ((X *ᵥ θstar + ε ω) - X *ᵥ (θhat ω)) ≤ dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θ) ((X *ᵥ θstar + ε ω) - X *ᵥ θ))
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤ Real.exp (s ^ 2 * σ ^ 2 / 2))
  (hsubG_int : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ) :
-- imply
  ∫ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ∂μ ≤ 16 * σ ^ 2 * ↑r := by
-- proof
  have hfund : ∀ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤
    2 * dotProduct (ε ω) (X *ᵥ (θhat ω - θstar)) := by
    intro ω
    exact thm_2_2_fundamental_inequality X θstar (ε ω) (θhat ω) (hLS ω)
  by_cases hσ : σ = 0
  ·
    subst hσ; simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_zero, zero_mul]
    exact subG_zero_sigma_integral_le_zero X θstar ε θhat hfund hsubG hsubG_int
  ·
    have hσ_pos : (0 : ℝ) < |σ| := abs_pos.mpr hσ
    have hσ_sq : σ ^ 2 = |σ| ^ 2 := (sq_abs σ).symm
    have hsubG' : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 →
      ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * |σ| ^ 2 / 2) := by
      intro v hv s
      rw [← hσ_sq]
      exact hsubG v hv s
    have hbound := sup_out_onb_expectation_bound X θstar ε θhat |σ| hσ_pos r hr hfund hsubG'
      hsubG_int
      (fun Z hZ_int hZ_exp hZ => subG_variance_bound Z |σ| hσ_pos hZ_int hZ_exp hZ)
    rwa [hσ_sq]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[thm_2_2_ls_expected_mse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma thm_2_2_ls_expected_mse
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [hprob : IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {θhat : Ω → Fin d → ℝ}
  {σ : ℝ}
  {r : ℕ}
-- given
  (hn : 0 < n)
  (hr : r = (X.transpose * X).rank)
  (hLS : ∀ ω, ∀ θ : Fin d → ℝ, dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ (θhat ω)) ((X *ᵥ θstar + ε ω) - X *ᵥ (θhat ω)) ≤ dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θ) ((X *ᵥ θstar + ε ω) - X *ᵥ θ))
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤ Real.exp (s ^ 2 * σ ^ 2 / 2))
  (hsubG_int : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ) :
-- imply
  ∫ ω, (1 / (n : ℝ)) * dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ∂μ ≤ 16 * σ ^ 2 * ↑r / ↑n := by
-- proof
  have hbound := subG_expected_squared_norm_bound hprob X θstar ε θhat σ r hr hLS hsubG hsubG_int
  rw [show (16 : ℝ) * σ ^ 2 * ↑r / ↑n = 1 / ↑n * (16 * σ ^ 2 * ↑r) from by ring]
  rw [integral_const_mul (1 / (n : ℝ))]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[bochner_mgf_of_lintegral_mgf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma bochner_mgf_of_lintegral_mgf
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  {X : Ω → ℝ}
  {σsq : ℝ}
  {s : ℝ}
-- given
  (hX : Measurable X)
  (hbound : ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω)) ∂μ ≤ ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2))) :
-- imply
  ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2) := by
-- proof
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun ω => le_of_lt (Real.exp_pos _)))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  exact ENNReal.toReal_le_of_le_ofReal (le_of_lt (Real.exp_pos _)) (hbound s)

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[exp_integrable_of_subG_mgf_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma exp_integrable_of_subG_mgf_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {σsq : ℝ}
  {s : ℝ}
-- given
  (hX : Measurable X)
  (hbound : ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω)) ∂μ ≤ ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2))) :
-- imply
  MeasureTheory.Integrable (fun ω => Real.exp (s * X ω)) μ := by
-- proof
  rw [← MeasureTheory.lintegral_ofReal_ne_top_iff_integrable]
  · intro h
    have hb := hbound s
    rw [h] at hb
    exact absurd hb (not_le.mpr ENNReal.ofReal_lt_top)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact Filter.Eventually.of_forall (fun ω => le_of_lt (Real.exp_pos _))

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[eq_zero_of_forall_mul_le_exp_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma eq_zero_of_forall_mul_le_exp_sub_one
  {c σsq : ℝ}
-- given
  (h : ∀ s : ℝ, s * c ≤ Real.exp (σsq * s ^ 2 / 2) - 1) :
-- imply
  c = 0 := by
-- proof
  set g := fun s => Real.exp (σsq * s ^ 2 / 2) - 1 - s * c with hg_def
  have hg_nonneg : ∀ s, 0 ≤ g s := fun s => by simp only [hg_def]; linarith [h s]
  have hg_zero : g 0 = 0 := by simp [hg_def]
  have hg_min : IsLocalMin g 0 := by
    show ∀ᶠ x in nhds 0, g 0 ≤ g x
    simp only [hg_zero]
    exact Filter.Eventually.of_forall (fun x => hg_nonneg x)
  have hg_deriv : HasDerivAt g (-c) 0 := by
    have hinner : HasDerivAt (fun s => σsq * s ^ 2 / 2) 0 0 := by
      have h := (hasDerivAt_pow 2 (0 : ℝ)).const_mul (σsq / 2)
      have : (fun x => σsq / 2 * x ^ 2) = (fun s => σsq * s ^ 2 / 2) := by ext; ring
      rw [this] at h; convert h using 1; norm_num
    have hexp : HasDerivAt (fun s => Real.exp (σsq * s ^ 2 / 2)) 0 0 := by
      have := hinner.exp; simp only [mul_zero] at this; exact this
    have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const 0 1
    have hlin : HasDerivAt (fun s => s * c) c 0 := by
      have := (hasDerivAt_id (0 : ℝ)).mul_const c; simp only [one_mul] at this; exact this
    convert (hexp.sub hconst).sub hlin using 1; ring
  linarith [hg_min.hasDerivAt_eq_zero hg_deriv]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[mean_zero_of_subG_mgf_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma mean_zero_of_subG_mgf_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {σsq : ℝ}
-- given
  (hXm : Measurable X)
  (hbound_lint : ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω)) ∂μ ≤ ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2))) :
-- imply
  ∫ ω, X ω ∂μ = 0 := by
-- proof
  have hbound : ∀ s : ℝ, ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2) :=
    bochner_mgf_of_lintegral_mgf _ hXm _ hbound_lint
  have hexp_int : ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * X ω)) μ :=
    exp_integrable_of_subG_mgf_bound _ hXm _ hbound_lint
  by_cases hX : MeasureTheory.Integrable X μ
  ·
    apply eq_zero_of_forall_mul_le_exp_sub_one _ σsq
    intro s
    have h1 : ∫ ω, (1 + s * X ω) ∂μ ≤ ∫ ω, Real.exp (s * X ω) ∂μ := by
      apply MeasureTheory.integral_mono
      · exact (MeasureTheory.integrable_const 1).add (hX.const_mul s)
      · exact hexp_int s
      · intro ω; linarith [Real.add_one_le_exp (s * X ω)]
    have h2 : ∫ ω, (1 + s * X ω) ∂μ = 1 + s * ∫ ω, X ω ∂μ := by
      rw [MeasureTheory.integral_add (MeasureTheory.integrable_const 1) (hX.const_mul s)]
      simp [MeasureTheory.integral_const, MeasureTheory.Measure.real,
        MeasureTheory.IsProbabilityMeasure.measure_univ, MeasureTheory.integral_const_mul]
    linarith [hbound s]
  · exact MeasureTheory.integral_undef hX

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[mgf_implies_isSubGaussian_onb_proj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma mgf_implies_isSubGaussian_onb_proj
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {n : ℕ}
  {r : ℕ}
  {Φ : Fin r → (Fin n → ℝ)}
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {a : EuclideanSpace ℝ (Fin r)}
-- given
  (hΦ_unit : ∀ i : Fin r, dotProduct (Φ i) (Φ i) = 1)
  (hΦ_ortho : ∀ i j : Fin r, i ≠ j → dotProduct (Φ i) (Φ j) = 0)
  (hσ : 0 < σ)
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) v)) ∂μ ≤ ENNReal.ofReal (Real.exp (s ^ 2 * σ ^ 2 / 2)))
  (hε_meas : ∀ j, Measurable (fun ω => ε ω j))
  (ha : ‖a‖ ≤ 1) :
-- imply
  IsSubGaussian (fun ω => @inner ℝ _ _ a ((WithLp.toLp 2 (fun i => dotProduct (ε ω) (Φ i)) : EuclideanSpace ℝ (Fin r)))) (σ ^ 2) μ := by
-- proof
  set w : Fin n → ℝ := fun j => ∑ i, a i * Φ i j with hw_def
  have hfun : (fun ω => @inner ℝ _ _ a
    ((WithLp.toLp 2 (fun i => dotProduct (ε ω) (Φ i)) : EuclideanSpace ℝ (Fin r)))) =
    (fun ω => dotProduct (ε ω) w) := by
    ext ω
    simp only [inner, dotProduct, starRingEnd_apply, star_trivial, RCLike.re_to_real]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hw_norm : dotProduct w w ≤ 1 := by
    show dotProduct (fun j => ∑ i, a i * Φ i j) (fun j => ∑ i, a i * Φ i j) ≤ 1
    have hw' : (fun j => ∑ i : Fin r, a i * Φ i j) = ∑ i : Fin r, (a i • Φ i) := by
      ext j; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hw', sum_dotProduct]
    conv_lhs => arg 2; ext i; rw [dotProduct_sum]
    simp_rw [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    have hdiag : (∑ i : Fin r, ∑ j : Fin r, a i * (a j * dotProduct (Φ i) (Φ j))) =
      ∑ i, (a i) ^ 2 := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_eq_single i]
      · simp [hΦ_unit i, sq]
      · intro j _ hji; have := hΦ_ortho i j (Ne.symm hji); simp [this]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hdiag]
    have hnorm : ∑ i, (a i) ^ 2 = ‖a‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      congr 1; ext i; rw [Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    exact pow_le_one₀ (norm_nonneg _) ha
  have hw_meas : Measurable (fun ω => dotProduct (ε ω) w) := by
    apply Finset.measurable_sum; intro j _
    exact (hε_meas j).mul_const _
  have hmgf_lint : ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) w)) ∂μ ≤
    ENNReal.ofReal (Real.exp (s ^ 2 * σ ^ 2 / 2)) := hsubG w hw_norm
  have hmgf_lint' : ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) w)) ∂μ ≤
    ENNReal.ofReal (Real.exp (σ ^ 2 * s ^ 2 / 2)) := by
    intro s; rw [show σ ^ 2 * s ^ 2 / 2 = s ^ 2 * σ ^ 2 / 2 from by ring]; exact hmgf_lint s
  have hexp_int : ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) w)) μ :=
    exp_integrable_of_subG_mgf_bound _ hw_meas _ hmgf_lint'
  have hmgf' : ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) w) ∂μ ≤
    Real.exp (σ ^ 2 * s ^ 2 / 2) :=
    bochner_mgf_of_lintegral_mgf _ hw_meas _ hmgf_lint'
  have hmgf : ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) w) ∂μ ≤
    Real.exp (s ^ 2 * σ ^ 2 / 2) := by
    intro s; rw [show s ^ 2 * σ ^ 2 / 2 = σ ^ 2 * s ^ 2 / 2 from by ring]; exact hmgf' s
  have hint := (integrable_of_mgf_bound (fun ω => dotProduct (ε ω) w) σ hmgf hexp_int).1
  rw [hfun]
  exact ⟨hint,
    mean_zero_of_subG_mgf_bound _ hw_meas _ hmgf_lint',
    hexp_int,
    hmgf'⟩

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[onb_projected_noise_tail_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma onb_projected_noise_tail_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {n : ℕ}
  {r : ℕ}
  {Φ : Fin r → (Fin n → ℝ)}
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {t : ℝ}
-- given
  (hr : 0 < r)
  (hΦ_unit : ∀ i : Fin r, dotProduct (Φ i) (Φ i) = 1)
  (hΦ_ortho : ∀ i j : Fin r, i ≠ j → dotProduct (Φ i) (Φ j) = 0)
  (hσ : 0 < σ)
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) v)) ∂μ ≤ ENNReal.ofReal (Real.exp (s ^ 2 * σ ^ 2 / 2)))
  (hε_meas : ∀ j, Measurable (fun ω => ε ω j))
  (ht : 0 < t) :
-- imply
  μ {ω | ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 > t ^ 2} ≤ ENNReal.ofReal ((6 : ℝ) ^ r * Real.exp (-(t ^ 2 / (8 * σ ^ 2)))) := by
-- proof
  set X_proj : Ω → EuclideanSpace ℝ (Fin r) :=
    fun ω => (WithLp.toLp 2 (fun i => dotProduct (ε ω) (Φ i)) : EuclideanSpace ℝ (Fin r))
  have h_sum_eq_norm : ∀ ω,
    ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 = ‖X_proj ω‖ ^ 2 := by
    intro ω
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    congr 1; ext i; simp [X_proj]
  have h_subset :
    {ω | ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 > t ^ 2} ⊆
    {ω | ∃ θ : EuclideanSpace ℝ (Fin r), ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ (X_proj ω) > t} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [h_sum_eq_norm] at hω
    have h_norm_pos : 0 ≤ ‖X_proj ω‖ := norm_nonneg _
    have h_norm_gt : ‖X_proj ω‖ > t := by
      nlinarith [sq_nonneg (‖X_proj ω‖ - t)]
    exact norm_gt_exists_inner_gt (X_proj ω) t ht h_norm_gt
  have hσ_sq : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have h_sg : ∀ (a : EuclideanSpace ℝ (Fin r)), ‖a‖ ≤ 1 →
    IsSubGaussian (fun ω => @inner ℝ _ _ a (X_proj ω)) (σ ^ 2) μ := by
    intro a ha
    exact mgf_implies_isSubGaussian_onb_proj Φ hΦ_unit hΦ_ortho ε σ hσ hsubG hε_meas a ha
  calc μ {ω | ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 > t ^ 2}
    ≤ μ {ω | ∃ θ : EuclideanSpace ℝ (Fin r), ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ (X_proj ω) > t} :=
      MeasureTheory.measure_mono h_subset
    _ ≤ ENNReal.ofReal ((6 : ℝ) ^ r * Real.exp (-(t ^ 2 / (8 * σ ^ 2)))) :=
      theorem_1_19_tail_bound hr hσ_sq h_sg t ht

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[six_lt_exp_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma six_lt_exp_two
-- imply
  (6:ℝ) < Real.exp 2 := by
-- proof
  have h1 : Real.exp 1 > (2718 : ℝ) / 1000 := by
    have := Real.exp_one_gt_d9; linarith
  nlinarith [show Real.exp 2 = Real.exp 1 * Real.exp 1 from by rw [← Real.exp_add]; norm_num]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[six_mul_exp_neg_two_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma six_mul_exp_neg_two_le_one
-- imply
  (6:ℝ) * Real.exp (-2) ≤ 1 := by
-- proof
  rw [show (1:ℝ) = Real.exp 2 * Real.exp (-2) from by rw [← Real.exp_add]; simp]
  nlinarith [six_lt_exp_two, Real.exp_pos (-2 : ℝ)]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[exp_neg_two_log_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma exp_neg_two_log_inv
  {δ : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  Real.exp (-2 * Real.log (1/δ)) = δ ^ 2 := by
-- proof
  have h1 : Real.log (1/δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  rw [h1, show -2 * -Real.log δ = 2 * Real.log δ from by ring,
    show (2 : ℝ) * Real.log δ = Real.log (δ ^ 2) from by rw [Real.log_pow]; ring]
  exact Real.exp_log (by positivity)

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[covering_number_bound_le_delta](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma covering_number_bound_le_delta
  {r : ℕ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hδ1 : δ ≤ 1) :
-- imply
  (6:ℝ)^r * Real.exp (-(2 * ↑r + 2 * Real.log (1/δ))) ≤ δ := by
-- proof
  rw [show -(2 * (r:ℝ) + 2 * Real.log (1/δ)) = ↑r * (-2) + (-2 * Real.log (1/δ)) from by ring,
    Real.exp_add, Real.exp_nat_mul, exp_neg_two_log_inv δ hδ]
  suffices h : (6 * Real.exp (-2)) ^ r * δ ^ 2 ≤ δ by
    convert h using 1; rw [mul_pow]; ring
  have h1 : (6 * Real.exp (-2)) ^ r ≤ 1 :=
    pow_le_one₀ (by positivity) six_mul_exp_neg_two_le_one
  nlinarith [show δ * δ ≤ 1 * δ from by nlinarith]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[le_four_mul_of_le_two_sqrt_mul_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma le_four_mul_of_le_two_sqrt_mul_sqrt
  {a b : ℝ}
-- given
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (h : a ≤ 2 * (Real.sqrt a * Real.sqrt b)) :
-- imply
  a ≤ 4 * b := by
-- proof
  by_cases h0 : Real.sqrt a = 0
  · rw [Real.sqrt_eq_zero ha] at h0; linarith
  · have hpos : 0 < Real.sqrt a := lt_of_le_of_ne (Real.sqrt_nonneg a) (Ne.symm h0)
    have h1 : Real.sqrt a ≤ 2 * Real.sqrt b := by
      have h2 : Real.sqrt a * Real.sqrt a ≤ Real.sqrt a * (2 * Real.sqrt b) := by
        nlinarith [Real.sq_sqrt ha]
      exact le_of_mul_le_mul_of_pos_left h2 hpos
    nlinarith [sq_nonneg (Real.sqrt a - 2 * Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[subG_chi_squared_tail_bound_from_thm_1_19](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma subG_chi_squared_tail_bound_from_thm_1_19
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {θhat : Ω → Fin d → ℝ}
  {σ : ℝ}
  {r : ℕ}
  {δ : ℝ}
-- given
  (hσ : 0 < σ)
  (hr : r = (X.transpose * X).rank)
  (hδ_pos : 0 < δ)
  (hδ_le : δ ≤ 1)
  (hfund : ∀ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤ 2 * dotProduct (ε ω) (X *ᵥ (θhat ω - θstar)))
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) v)) ∂μ ≤ ENNReal.ofReal (Real.exp (s ^ 2 * σ ^ 2 / 2)))
  (hε_meas : ∀ j, Measurable (fun ω => ε ω j)) :
-- imply
  μ {ω : Ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) > 64 * σ ^ 2 * (↑r + Real.log (1 / δ))} ≤ ENNReal.ofReal δ := by
-- proof
  obtain ⟨Φ, hΦ_unit, hΦ_ortho, hΦ_parseval, hΦ_expand⟩ := exists_onb_with_parseval X r hr
  have h_event_contain : ∀ ω,
    dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤
    4 * ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 := by
    intro ω
    set v := X *ᵥ (θhat ω - θstar)
    have hf := hfund ω
    have hpars := hΦ_parseval (θhat ω - θstar)
    have hexp := hΦ_expand (ε ω) (θhat ω - θstar)
    have ha_nn : 0 ≤ dotProduct v v :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
    have hb_nn : 0 ≤ ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h1 : dotProduct v v ≤
      2 * ∑ i : Fin r, dotProduct v (Φ i) * dotProduct (ε ω) (Φ i) := by linarith
    have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => dotProduct v (Φ i)) (fun i => dotProduct (ε ω) (Φ i))
    have h2 : dotProduct v v ≤ 2 * (Real.sqrt (dotProduct v v) *
      Real.sqrt (∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2)) := by
      calc dotProduct v v
        ≤ 2 * ∑ i : Fin r, dotProduct v (Φ i) * dotProduct (ε ω) (Φ i) := h1
        _ ≤ 2 * (Real.sqrt (∑ i : Fin r, (dotProduct v (Φ i)) ^ 2) *
          Real.sqrt (∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2)) := by gcongr
        _ = 2 * (Real.sqrt (dotProduct v v) *
          Real.sqrt (∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2)) := by rw [hpars]
    exact le_four_mul_of_le_two_sqrt_mul_sqrt _ _ ha_nn hb_nn h2
  set C := 64 * σ ^ 2 * (↑r + Real.log (1 / δ))
  by_cases hr0 : r = 0
  ·
    subst hr0
    have : ∀ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤ 0 := by
      intro ω; have := h_event_contain ω
      simp only [Fin.sum_univ_zero, mul_zero] at this
      exact this
    have h_empty : {ω : Ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) > C} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h1 := this ω
      have h2 : (0 : ℝ) ≤ C := by
        simp only [C]
        have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ_pos]; linarith)
        positivity
      linarith
    rw [h_empty, MeasureTheory.measure_empty]
    exact zero_le _
  ·
    have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
    set t := Real.sqrt (16 * σ ^ 2 * (↑r + Real.log (1 / δ))) with ht_def
    have hσ_sq : 0 < σ ^ 2 := by positivity
    have hlog_pos : 0 ≤ Real.log (1 / δ) := by
      apply Real.log_nonneg; rw [le_div_iff₀ hδ_pos]; linarith
    have ht_sq : t ^ 2 = 16 * σ ^ 2 * (↑r + Real.log (1 / δ)) := by
      rw [ht_def, Real.sq_sqrt (by positivity)]
    have ht_pos : 0 < t := by rw [ht_def]; apply Real.sqrt_pos_of_pos; positivity
    have htail := onb_projected_noise_tail_bound hr_pos Φ hΦ_unit hΦ_ortho ε σ hσ hsubG hε_meas t ht_pos
    have h_subset : {ω : Ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) > C} ⊆
      {ω | ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 > t ^ 2} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have := h_event_contain ω
      rw [ht_sq]; show _ > _; linarith
    calc μ {ω : Ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) > C}
      ≤ μ {ω | ∑ i : Fin r, (dotProduct (ε ω) (Φ i)) ^ 2 > t ^ 2} :=
        MeasureTheory.measure_mono h_subset
      _ ≤ ENNReal.ofReal ((6 : ℝ) ^ r * Real.exp (-(t ^ 2 / (8 * σ ^ 2)))) := htail
      _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        rw [ht_sq]
        rw [show 16 * σ ^ 2 * (↑r + Real.log (1/δ)) / (8 * σ ^ 2) =
          2 * ↑r + 2 * Real.log (1/δ) from by field_simp; ring]
        exact covering_number_bound_le_delta r δ hδ_pos hδ_le

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[subG_squared_norm_high_prob_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma subG_squared_norm_high_prob_bound
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {θhat : Ω → Fin d → ℝ}
  {σ : ℝ}
  {r : ℕ}
  {δ : ℝ}
-- given
  (hσ : 0 < σ)
  (hr : r = (X.transpose * X).rank)
  (hδ_pos : 0 < δ)
  (hδ_le : δ ≤ 1)
  (hfund : ∀ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤ 2 * dotProduct (ε ω) (X *ᵥ (θhat ω - θstar)))
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) v)) ∂μ ≤ ENNReal.ofReal (Real.exp (s ^ 2 * σ ^ 2 / 2)))
  (hε_meas : ∀ j, Measurable (fun ω => ε ω j)) :
-- imply
  μ {ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤ 64 * σ ^ 2 * (↑r + Real.log (1 / δ))} ≥ ENNReal.ofReal (1 - δ) := by
-- proof
  set C := 64 * σ ^ 2 * (↑r + Real.log (1 / δ)) with hC_def
  set S := {ω : Ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤ C}
  suffices hmain : μ Sᶜ ≤ ENNReal.ofReal δ by
    rw [ge_iff_le, ENNReal.ofReal_sub _ (le_of_lt hδ_pos),
      show ENNReal.ofReal 1 = 1 from by simp, tsub_le_iff_right]
    calc (1 : ENNReal) = μ Set.univ := (MeasureTheory.measure_univ).symm
      _ ≤ μ S + μ Sᶜ := MeasureTheory.measure_univ_le_add_compl S
      _ ≤ μ S + ENNReal.ofReal δ := by gcongr
  have htail := subG_chi_squared_tail_bound_from_thm_1_19 X θstar ε θhat σ hσ r hr δ hδ_pos hδ_le hfund hsubG hε_meas
  have hset_eq : Sᶜ = {ω : Ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) > C} := by
    ext ω
    simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  rwa [hset_eq]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[thm_2_2_ls_high_prob_mse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma thm_2_2_ls_high_prob_mse
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {θhat : Ω → Fin d → ℝ}
  {σ : ℝ}
  {r : ℕ}
  {δ : ℝ}
-- given
  (hn : 0 < n)
  (hσ : 0 < σ)
  (hr : r = (X.transpose * X).rank)
  (hδ_pos : 0 < δ)
  (hδ_le : δ ≤ 1)
  (hLS : ∀ ω, ∀ θ : Fin d → ℝ, dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ (θhat ω)) ((X *ᵥ θstar + ε ω) - X *ᵥ (θhat ω)) ≤ dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θ) ((X *ᵥ θstar + ε ω) - X *ᵥ θ))
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) v)) ∂μ ≤ ENNReal.ofReal (Real.exp (s ^ 2 * σ ^ 2 / 2)))
  (hε_meas : ∀ j, Measurable (fun ω => ε ω j)) :
-- imply
  μ {ω | (1 / (n : ℝ)) * dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤ 64 * σ ^ 2 * (↑r + Real.log (1 / δ)) / ↑n} ≥ ENNReal.ofReal (1 - δ) := by
-- proof
  have hfund : ∀ ω, dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤
    2 * dotProduct (ε ω) (X *ᵥ (θhat ω - θstar)) := by
    intro ω
    exact thm_2_2_fundamental_inequality X θstar (ε ω) (θhat ω) (hLS ω)
  have hHP := subG_squared_norm_high_prob_bound X θstar ε θhat σ hσ r hr δ hδ_pos hδ_le
    hfund hsubG hε_meas
  have hset : {ω | (1 / (n : ℝ)) *
    dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤
    64 * σ ^ 2 * (↑r + Real.log (1 / δ)) / ↑n} =
    {ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤
      64 * σ ^ 2 * (↑r + Real.log (1 / δ))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [show (1 : ℝ) / n * dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) =
      dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) / n by ring]
    exact div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hn)
  rwa [hset]

end Rigollet.Chapter2

namespace Rigollet.Chapter2

/--
[thm_2_2_ridge_risk_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_2.lean)
-/
@[path]
lemma thm_2_2_ridge_risk_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {ε : Ω → Fin n → ℝ}
  {θhat : Ω → Fin d → ℝ}
  {σ : ℝ}
  {r : ℕ}
  {δ : ℝ}
-- given
  (hn : 0 < n)
  (hσ : 0 < σ)
  (hr : r = (X.transpose * X).rank)
  (hδ_pos : 0 < δ)
  (hδ_le : δ ≤ 1)
  (hLS : ∀ ω, ∀ θ : Fin d → ℝ, dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ (θhat ω)) ((X *ᵥ θstar + ε ω) - X *ᵥ (θhat ω)) ≤ dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θ) ((X *ᵥ θstar + ε ω) - X *ᵥ θ))
  (hsubG : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 → ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) v)) ∂μ ≤ ENNReal.ofReal (Real.exp (s ^ 2 * σ ^ 2 / 2)))
  (hε_meas : ∀ j, Measurable (fun ω => ε ω j)) :
-- imply
  (∫ ω, (1 / (n : ℝ)) * dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ∂μ ≤ 16 * σ ^ 2 * ↑r / ↑n) ∧ (μ {ω | (1 / (n : ℝ)) * dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤ 64 * σ ^ 2 * (↑r + Real.log (1 / δ)) / ↑n} ≥ ENNReal.ofReal (1 - δ)) := by
-- proof
  have hsubG_bochner : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 →
    ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
      Real.exp (s ^ 2 * σ ^ 2 / 2) := by
    intro v hv s
    have hw_meas : Measurable (fun ω => dotProduct (ε ω) v) := by
      apply Finset.measurable_sum; intro j _; exact (hε_meas j).mul_const _
    have hmgf_lint' : ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) v)) ∂μ ≤
      ENNReal.ofReal (Real.exp (σ ^ 2 * s ^ 2 / 2)) := by
      intro s'; rw [show σ ^ 2 * s' ^ 2 / 2 = s' ^ 2 * σ ^ 2 / 2 from by ring]
      exact hsubG v hv s'
    have := bochner_mgf_of_lintegral_mgf _ hw_meas _ hmgf_lint' s
    rwa [show σ ^ 2 * s ^ 2 / 2 = s ^ 2 * σ ^ 2 / 2 from by ring] at this
  have hsubG_int : ∀ (v : Fin n → ℝ), dotProduct v v ≤ 1 →
    ∀ s : ℝ, Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ := by
    intro v hv s
    have hw_meas : Measurable (fun ω => dotProduct (ε ω) v) := by
      apply Finset.measurable_sum; intro j _; exact (hε_meas j).mul_const _
    have hmgf_lint' : ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) v)) ∂μ ≤
      ENNReal.ofReal (Real.exp (σ ^ 2 * s ^ 2 / 2)) := by
      intro s'; rw [show σ ^ 2 * s' ^ 2 / 2 = s' ^ 2 * σ ^ 2 / 2 from by ring]
      exact hsubG v hv s'
    exact exp_integrable_of_subG_mgf_bound _ hw_meas _ hmgf_lint' s
  exact ⟨thm_2_2_ls_expected_mse hn X θstar ε θhat σ r hr hLS hsubG_bochner hsubG_int,
    thm_2_2_ls_high_prob_mse hn X θstar ε θhat σ hσ r hr δ hδ_pos hδ_le hLS hsubG hε_meas⟩

end Rigollet.Chapter2


-- created on 2026-10-23
