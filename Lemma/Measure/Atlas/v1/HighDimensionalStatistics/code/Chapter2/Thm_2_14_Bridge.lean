import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_14_Bridge
open Matrix MeasureTheory Metric Set Real ENNReal Finset


/--
[dotProduct_eq_inner_euclidean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_Bridge.lean)
-/
@[path]
lemma dotProduct_eq_inner_euclidean
  {n : ℕ}
  {v w : Fin n → ℝ} :
-- imply
  dotProduct v w = @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (toEuc n v) (toEuc n w) := by
-- proof
  simp only [PiLp.inner_apply, WithLp.equiv_symm_apply, dotProduct, toEuc]
  congr 1; ext i
  simp [inner, Inner.inner, mul_comm]

/--
[euclidean_norm_eq_sqrt_dotProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_Bridge.lean)
-/
@[path]
lemma euclidean_norm_eq_sqrt_dotProduct
  {n : ℕ}
  {v : Fin n → ℝ} :
-- imply
  ‖toEuc n v‖ = Real.sqrt (dotProduct v v) := by
-- proof
  have h : dotProduct v v = ‖toEuc n v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [dotProduct, WithLp.equiv_symm_apply, toEuc]
    congr 1; ext i; simp [sq_abs]; ring
  rw [h, Real.sqrt_sq (norm_nonneg _)]

/--
[euclidean_norm_le_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_Bridge.lean)
-/
@[path]
lemma euclidean_norm_le_one_iff
  {n : ℕ}
  {v : Fin n → ℝ} :
-- imply
  ‖toEuc n v‖ ≤ 1 ↔ dotProduct v v ≤ 1 := by
-- proof
  rw [euclidean_norm_eq_sqrt_dotProduct, sqrt_le_one]

/--
[subgaussian_inner_from_dotProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_Bridge.lean)
-/
@[path]
lemma subgaussian_inner_from_dotProduct
  {p : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {Z : Ω → Fin p → ℝ}
  {σsq : ℝ}
  {θ : EuclideanSpace ℝ (Fin p)}
-- given
  (hsg : ∀ (a : Fin p → ℝ), dotProduct a a ≤ 1 → IsSubGaussian (fun ω => dotProduct a (Z ω)) σsq μ)
  (hθ : ‖θ‖ ≤ 1) :
-- imply
  IsSubGaussian (fun ω => @inner ℝ _ _ θ (toEuc p (Z ω))) σsq μ := by
-- proof
  have hconv : ∀ ω, @inner ℝ (EuclideanSpace ℝ (Fin p)) _ θ (toEuc p (Z ω)) =
    dotProduct (fromEuc p θ) (Z ω) := by
    intro ω
    conv_lhs => rw [show θ = toEuc p (fromEuc p θ) from
      ((WithLp.equiv 2 (Fin p → ℝ)).symm_apply_apply θ).symm]
    exact (dotProduct_eq_inner_euclidean (fromEuc p θ) (Z ω)).symm
  have hunit : dotProduct (fromEuc p θ) (fromEuc p θ) ≤ 1 := by
    rw [← euclidean_norm_le_one_iff]
    rw [show toEuc p (fromEuc p θ) = θ from
      (WithLp.equiv 2 (Fin p → ℝ)).symm_apply_apply θ]
    exact hθ
  have h := hsg (fromEuc p θ) hunit
  simp_rw [hconv]
  exact h

/--
[subgaussian_inner_from_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_Bridge.lean)
-/
@[path]
lemma subgaussian_inner_from_coord
  {n : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {ε : Ω → Fin n → ℝ}
  {σsq : ℝ}
  {a : EuclideanSpace ℝ (Fin n)}
-- given
  (hσ : 0 ≤ σsq)
  (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) σsq μ)
  (hε_indep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
  (hε_meas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
  (ha : ‖a‖ ≤ 1) :
-- imply
  IsSubGaussian (fun ω => @inner ℝ _ _ a (toEuc n (ε ω))) σsq μ := by
-- proof
  apply subgaussian_inner_from_dotProduct _ a ha
  intro v hv
  have hdot_eq : ∀ ω, dotProduct v (ε ω) = ∑ i : Fin n, v i * ε ω i := by
    intro ω; simp only [dotProduct]
  simp_rw [hdot_eq]
  have h16 := theorem_1_6_subgaussian_vector hε hε_indep hε_meas v
  have hdvv : ∑ i : Fin n, v i ^ 2 = dotProduct v v := by
    simp only [dotProduct]; congr 1; ext i; ring
  exact h16.mono_variance (by
    rw [hdvv]
    calc σsq * dotProduct v v ≤ σsq * 1 := mul_le_mul_of_nonneg_left hv hσ
      _ = σsq := mul_one _)

/--
[theorem_1_19_tail_bound_vec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_Bridge.lean)
-/
@[path]
lemma theorem_1_19_tail_bound_vec
  {p : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {Z : Ω → Fin p → ℝ}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hp : 0 < p)
  (hσ : 0 < σsq)
  (hsg : ∀ (a : Fin p → ℝ), dotProduct a a ≤ 1 → IsSubGaussian (fun ω => dotProduct a (Z ω)) σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | ∃ θ : Fin p → ℝ, dotProduct θ θ ≤ 1 ∧ dotProduct θ (Z ω) > t} ≤ ENNReal.ofReal ((6 : ℝ) ^ p * Real.exp (-(t ^ 2 / (8 * σsq)))) := by
-- proof
  set X' : Ω → EuclideanSpace ℝ (Fin p) := fun ω => toEuc p (Z ω) with hX'_def
  have hsg' : ∀ (a : EuclideanSpace ℝ (Fin p)), ‖a‖ ≤ 1 →
    IsSubGaussian (fun ω => @inner ℝ _ _ a (X' ω)) σsq μ := by
    intro a ha
    exact subgaussian_inner_from_dotProduct hsg a ha
  have h_tail := theorem_1_19_tail_bound hp hσ hsg' t ht
  suffices h_eq :
    {ω | ∃ θ : Fin p → ℝ, dotProduct θ θ ≤ 1 ∧ dotProduct θ (Z ω) > t} =
    {ω | ∃ θ' : EuclideanSpace ℝ (Fin p), ‖θ'‖ ≤ 1 ∧
      @inner ℝ _ _ θ' (X' ω) > t} by
    rw [h_eq]; exact h_tail
  ext ω
  constructor
  ·
    rintro ⟨θ, hθ_unit, hθ_inner⟩
    refine ⟨toEuc p θ, ?_, ?_⟩
    · rwa [euclidean_norm_le_one_iff]
    · rw [hX'_def, ← dotProduct_eq_inner_euclidean]
      exact hθ_inner
  ·
    rintro ⟨θ', hθ'_norm, hθ'_inner⟩
    refine ⟨fromEuc p θ', ?_, ?_⟩
    · rw [← euclidean_norm_le_one_iff]
      rwa [show toEuc p (fromEuc p θ') = θ' from
        (WithLp.equiv 2 (Fin p → ℝ)).symm_apply_apply θ']
    · rw [hX'_def] at hθ'_inner
      conv at hθ'_inner =>
        arg 1; rw [show θ' = toEuc p (fromEuc p θ') from
          ((WithLp.equiv 2 (Fin p → ℝ)).symm_apply_apply θ').symm]
      rwa [← dotProduct_eq_inner_euclidean] at hθ'_inner


-- created on 2026-10-23
