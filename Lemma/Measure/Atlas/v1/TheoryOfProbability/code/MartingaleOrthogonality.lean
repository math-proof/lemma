import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfProbability.code.MartingaleOrthogonality
open MeasureTheory Filter
open scoped MeasureTheory


/--
[integrable_of_sq_integrable_finite_measure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MartingaleOrthogonality.lean)
-/
@[path]
lemma integrable_of_sq_integrable_finite_measure
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsFiniteMeasure μ]
  {Y : Ω → ℝ}
-- given
  (hY_asm : AEStronglyMeasurable Y μ)
  (hY2 : Integrable (fun ω => Y ω ^ 2) μ) :
-- imply
  Integrable Y μ := by
-- proof
  apply Integrable.mono' (hY2.add (integrable_const 1)) hY_asm
  filter_upwards with ω
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_abs (Y ω), sq_nonneg (|Y ω| - 1)]

/--
[integrable_mul_of_sq_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MartingaleOrthogonality.lean)
-/
@[path]
lemma integrable_mul_of_sq_integrable
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {f g : Ω → ℝ}
-- given
  (hf : Integrable f μ)
  (hg : Integrable g μ)
  (hf2 : Integrable (fun ω => (f ω) ^ 2) μ)
  (hg2 : Integrable (fun ω => (g ω) ^ 2) μ) :
-- imply
  Integrable (fun ω => f ω * g ω) μ := by
-- proof
  apply Integrable.mono' ((hf2.add hg2).const_mul (1 / 2))
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards with ω
  simp only [Real.norm_eq_abs, Pi.add_apply, Pi.mul_apply]
  have hab : |f ω * g ω| ≤ 1 / 2 * (f ω ^ 2 + g ω ^ 2) := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|f ω| - |g ω|), sq_abs (f ω), sq_abs (g ω)]
  linarith [abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 * (f ω ^ 2 + g ω ^ 2) by
    nlinarith [sq_nonneg (f ω), sq_nonneg (g ω)])]

/--
[martingale_orthogonal_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MartingaleOrthogonality.lean)
-/
@[path]
lemma martingale_orthogonal_general
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}
  {X : ℕ → Ω → ℝ}
  {m n : ℕ}
  {Y : Ω → ℝ}
-- given
  (hmart : Martingale X ℱ μ)
  (hmn : m ≤ n)
  (hY_meas : StronglyMeasurable[ℱ m] Y)
  (hY_int : Integrable (fun ω => (Y ω) ^ 2) μ)
  (hX_sq : ∀ k, Integrable (fun ω => (X k ω) ^ 2) μ) :
-- imply
  ∫ ω, (X n ω - X m ω) * Y ω ∂μ = 0 := by
-- proof
  have hY_int1 : Integrable Y μ :=
    integrable_of_sq_integrable_finite_measure
      (hY_meas.mono (ℱ.le m)).aestronglyMeasurable hY_int
  have hXdiff_int : Integrable (X n - X m) μ :=
    (hmart.integrable n).sub (hmart.integrable m)
  have hXdiff_sq : Integrable (fun ω => (X n ω - X m ω) ^ 2) μ := by
    apply Integrable.mono' (((hX_sq n).add (hX_sq m)).const_mul 2)
      (hXdiff_int.aestronglyMeasurable.pow _)
    filter_upwards with ω
    simp only [Real.norm_eq_abs, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (X n ω + X m ω)]
  have hprod_int : Integrable (fun ω => Y ω * (X n ω - X m ω)) μ :=
    integrable_mul_of_sq_integrable hY_int1 hXdiff_int hY_int hXdiff_sq
  have hcondexp_diff_zero : μ[X n - X m | ℱ m] =ᵐ[μ] (0 : Ω → ℝ) :=
    (condExp_sub (hmart.integrable n) (hmart.integrable m) (ℱ m)).trans
      ((hmart.condExp_ae_eq hmn).sub (hmart.condExp_ae_eq (le_refl m)) |>.mono fun ω hω => by
        simp only [Pi.sub_apply, Pi.zero_apply] at hω ⊢; linarith)
  have hcond_prod_zero : μ[fun ω => Y ω * (X n ω - X m ω) | ℱ m] =ᵐ[μ] (0 : Ω → ℝ) :=
    (condExp_mul_of_stronglyMeasurable_left hY_meas hprod_int hXdiff_int).trans
      (hcondexp_diff_zero.mono fun ω hω => by
        simp only [Pi.mul_apply, Pi.zero_apply] at *
        show Y ω * (μ[X n - X m | ℱ m]) ω = 0
        rw [hω, mul_zero])
  calc ∫ ω, (X n ω - X m ω) * Y ω ∂μ
    = ∫ ω, Y ω * (X n ω - X m ω) ∂μ := by congr 1; ext ω; ring
    _ = ∫ ω, (μ[fun ω => Y ω * (X n ω - X m ω) | ℱ m]) ω ∂μ :=
      (integral_condExp (ℱ.le m)).symm
    _ = ∫ ω, (0 : ℝ) ∂μ := integral_congr_ae hcond_prod_zero
    _ = 0 := by simp


-- created on 2026-10-23
