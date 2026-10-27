import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.ProjectionTheory.code.MainLemma2R.Part3
open MeasureTheory Metric Set Finset ProjectionTheory
open scoped Classical InnerProductSpace


namespace ProjectionTheory

/--
[l2_norm_bilinear_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean)
-/
@[path]
lemma l2_norm_bilinear_expansion
  {ι : Type}
  [Fintype ι]
  {φ : ι → EuclideanSpace ℝ (Fin 2) → ℝ}
-- given
  (hφ : ∀ i j, Integrable (fun x => φ i x * φ j x) volume) :
-- imply
  ∫ x, (∑ i : ι, φ i x) ^ 2 = ∑ i : ι, ∑ j : ι, ∫ x, φ i x * φ j x := by
-- proof
  have h_pw : ∀ x, (∑ i : ι, φ i x) ^ 2 = ∑ i : ι, ∑ j : ι, φ i x * φ j x := by
    intro x
    rw [sq, Finset.sum_mul]
    congr 1; ext i; rw [Finset.mul_sum]
  simp_rw [h_pw]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hφ i j))]
  congr 1; ext i
  rw [integral_finset_sum _ (fun j _ => hφ i j)]

end ProjectionTheory

namespace ProjectionTheory

/--
[tube_inner_product_multiplicity_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean)
-/
@[path]
lemma tube_inner_product_multiplicity_bound
  {S : TubeCollection}
  {r : ℝ}
  {φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ}
-- given
  (hr_scale : r ∈ dyadicScales S.R)
  (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0)
  (hφ_inner_bound : ∀ i j, |∫ x, φ i x * φ j x| ≤ S.R / r)
  (hφ_sparse : ∀ i, (Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0)).card ≤ S.multiplicity r) :
-- imply
  ∀ i : S.ι, ∑ j : S.ι, |∫ x, φ i x * φ j x| ≤ (S.multiplicity r : ℝ) * (S.R / r) := by
-- proof
  intro i
  have hRr : (0 : ℝ) ≤ S.R / r := by
    apply div_nonneg
    · linarith [S.hR]
    · obtain ⟨k, _, hk1, _⟩ := hr_scale; linarith
  calc ∑ j : S.ι, |∫ x, φ i x * φ j x|
    = ∑ j ∈ Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0),
      |∫ x, φ i x * φ j x|
      + ∑ j ∈ Finset.univ.filter (fun j => ¬((∫ x, φ i x * φ j x) ≠ 0)),
        |∫ x, φ i x * φ j x| := by
      rw [Finset.sum_filter_add_sum_filter_not]
    _ = ∑ j ∈ Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0),
      |∫ x, φ i x * φ j x| := by
      have h0 : ∑ j ∈ Finset.univ.filter (fun j => ¬((∫ x, φ i x * φ j x) ≠ 0)),
        |∫ x, φ i x * φ j x| = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
        rw [hj, abs_zero]
      linarith
    _ ≤ ∑ _j ∈ Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0),
      (S.R / r) := by
      apply Finset.sum_le_sum; intro j _; exact hφ_inner_bound i j
    _ = (Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0)).card
      * (S.R / r) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S.multiplicity r : ℝ) * (S.R / r) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hφ_sparse i
      · exact hRr

end ProjectionTheory

namespace ProjectionTheory

/--
[per_scale_l2_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean)
-/
@[path]
lemma per_scale_l2_bound
  {S : TubeCollection}
  {r : ℝ}
  {f_r : EuclideanSpace ℝ (Fin 2) → ℝ}
-- given
  (hr_scale : r ∈ dyadicScales S.R)
  (h_fourier : ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ > 1 / r → fourierTransformR2 f_r ξ = 0)
  (h_tube_decomp : ∃ (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ), (∀ i, Integrable (φ i) volume) ∧ (∀ i j, Integrable (fun x => φ i x * φ j x) volume) ∧ (∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0) ∧ (∀ x, f_r x = ∑ i : S.ι, φ i x) ∧ (∀ i j, |∫ x, φ i x * φ j x| ≤ S.R / r) ∧ (∀ i, (Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0)).card ≤ S.multiplicity r)) :
-- imply
  ∫ x, (f_r x) ^ 2 ≤ (Fintype.card S.ι : ℝ) * (S.multiplicity r : ℝ) * (S.R / r) := by
-- proof
  obtain ⟨φ, _, hφ_prod_int, hφ_freq, hφ_sum, hφ_inner, hφ_sparse⟩ := h_tube_decomp
  have h_expand : ∫ x, (f_r x) ^ 2 = ∑ i : S.ι, ∑ j : S.ι, ∫ x, φ i x * φ j x := by
    conv_lhs => rw [show f_r = fun x => ∑ i : S.ι, φ i x from funext hφ_sum]
    exact l2_norm_bilinear_expansion φ hφ_prod_int
  have h_ortho := tube_inner_product_multiplicity_bound S r hr_scale φ hφ_freq hφ_inner hφ_sparse
  rw [h_expand]
  calc ∑ i : S.ι, ∑ j : S.ι, ∫ x, φ i x * φ j x
    ≤ ∑ i : S.ι, ∑ j : S.ι, |∫ x, φ i x * φ j x| := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      exact le_abs_self _
    _ = ∑ i : S.ι, (∑ j : S.ι, |∫ x, φ i x * φ j x|) := rfl
    _ ≤ ∑ i : S.ι, ((S.multiplicity r : ℝ) * (S.R / r)) := by
      apply Finset.sum_le_sum; intro i _; exact h_ortho i
    _ = (Fintype.card S.ι : ℝ) * (S.multiplicity r : ℝ) * (S.R / r) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end ProjectionTheory

namespace ProjectionTheory

/--
[abs_integral_mul_le_of_sq_integral_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean)
-/
@[path]
lemma abs_integral_mul_le_of_sq_integral_le
  [MeasurableSpace α]
  {μ : MeasureTheory.Measure α}
  {f g : α → ℝ}
  {A : ℝ}
-- given
  (hf2_int : Integrable (fun x => (f x) ^ 2) μ)
  (hg2_int : Integrable (fun x => (g x) ^ 2) μ)
  (hf_bound : ∫ x, (f x) ^ 2 ∂μ ≤ A)
  (hg_bound : ∫ x, (g x) ^ 2 ∂μ ≤ A) :
-- imply
  |∫ x, f x * g x ∂μ| ≤ A := by
-- proof
  have h1 : |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := by
    have := norm_integral_le_integral_norm (μ := μ) (fun x => f x * g x)
    simp only [Real.norm_eq_abs] at this
    exact this
  have h2 : ∫ x, |f x * g x| ∂μ ≤ ∫ x, ((f x) ^ 2 + (g x) ^ 2) / 2 ∂μ := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun x => abs_nonneg _)
    · exact (hf2_int.add hg2_int).div_const 2
    · apply ae_of_all _; intro x
      simp only
      rw [abs_mul]
      have := two_mul_le_add_sq (|f x|) (|g x|)
      rw [sq_abs, sq_abs] at this
      linarith
  have h3 : ∫ x, ((f x) ^ 2 + (g x) ^ 2) / 2 ∂μ ≤ A := by
    rw [integral_div, integral_add hf2_int hg2_int]
    linarith
  linarith

end ProjectionTheory

namespace ProjectionTheory

/--
[self_norm_from_amplitude](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean)
-/
@[path]
lemma self_norm_from_amplitude
  {ι : Type}
  [Fintype ι]
  {φ : ι → EuclideanSpace ℝ (Fin 2) → ℝ}
  {R r : ℝ}
  {g : ι → EuclideanSpace ℝ (Fin 2) → ℝ}
-- given
  (hφ_sq_int : ∀ i, Integrable (fun x => (φ i x) ^ 2) volume)
  (hg_int : ∀ i, Integrable (g i) volume)
  (h_pw : ∀ i, ∀ x, (φ i x) ^ 2 ≤ g i x)
  (h_integral_bound : ∀ i, ∫ x, g i x ≤ R / r) :
-- imply
  ∀ i, ∫ x, (φ i x) ^ 2 ≤ R / r := by
-- proof
  intro i
  calc ∫ x, (φ i x) ^ 2 ≤ ∫ x, g i x := by
    apply integral_mono (hφ_sq_int i) (hg_int i)
    intro x; exact h_pw i x
    _ ≤ R / r := h_integral_bound i
/-- Angular Fourier disjointness: if the directions of tubes $i, j$ make a large enough
angle (so $|\langle d_i, d_j\rangle| < 1 - (r/R)^2/2$), then the Fourier supports of
their pieces $\varphi_i$ and $\varphi_j$ are disjoint. -/
end ProjectionTheory



-- created on 2026-10-23
