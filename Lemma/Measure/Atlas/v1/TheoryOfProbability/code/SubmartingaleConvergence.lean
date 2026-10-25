import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.SubmartingaleConvergence
open MeasureTheory Filter Topology


/--
[submartingale_integral_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/SubmartingaleConvergence.lean)
-/
@[path]
lemma submartingale_integral_mono
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}
  {X : ℕ → Ω → ℝ}
  {i j : ℕ}
-- given
  (hsub : Submartingale X ℱ μ)
  (hij : i ≤ j) :
-- imply
  ∫ ω, X i ω ∂μ ≤ ∫ ω, X j ω ∂μ := by
-- proof
  have h_ae := hsub.2.1 i j hij
  calc ∫ ω, X i ω ∂μ
    ≤ ∫ ω, μ[X j | ↑(ℱ i)] ω ∂μ :=
      integral_mono_ae (hsub.2.2 i) integrable_condExp h_ae
    _ = ∫ ω, X j ω ∂μ := integral_condExp (ℱ.le i) (μ := μ)

/--
[submartingale_integral_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/SubmartingaleConvergence.lean)
-/
@[path]
lemma submartingale_integral_norm_le
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}
  {X : ℕ → Ω → ℝ}
  {C : ℝ}
  {n : ℕ}
-- given
  (hsub : Submartingale X ℱ μ)
  (hbdd : ∀ n, ∫ ω, (X n ω)⁺ ∂μ ≤ C) :
-- imply
  ∫ ω, ‖X n ω‖ ∂μ ≤ 2 * C - ∫ ω, X 0 ω ∂μ := by
-- proof
  have hint := hsub.2.2
  have hmax : Integrable (fun ω => (X n ω)⁺) μ := (hint n).sup (integrable_zero _ _ μ)
  have key : ∫ ω, ‖X n ω‖ ∂μ = 2 * ∫ ω, (X n ω)⁺ ∂μ - ∫ ω, X n ω ∂μ := by
    have kk : ∀ ω, ‖X n ω‖ = 2 * (X n ω)⁺ - X n ω := by
      intro ω
      simp only [Real.norm_eq_abs, posPart]
      obtain h | h := le_or_gt (X n ω) 0
      · simp [abs_of_nonpos h, max_eq_right h]
      · simp [abs_of_pos h, max_eq_left h.le]; ring
    simp_rw [kk]
    rw [integral_sub (hmax.const_mul 2) (hint n)]
    congr 1; exact integral_const_mul 2 _
  have hmono : ∫ ω, X 0 ω ∂μ ≤ ∫ ω, X n ω ∂μ :=
    submartingale_integral_mono hsub (Nat.zero_le n)
  linarith [hbdd n]

/--
[submartingale_ae_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/SubmartingaleConvergence.lean)
-/
@[path]
lemma submartingale_ae_convergence
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}
  {X : ℕ → Ω → ℝ}
  {C : ℝ}
-- given
  (hsub : Submartingale X ℱ μ)
  (hbdd : ∀ n, ∫ ω, (X n ω)⁺ ∂μ ≤ C) :
-- imply
  ∃ X_inf : Ω → ℝ, Integrable X_inf μ ∧ ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (X_inf ω)) := by
-- proof
  have hint : ∀ n, Integrable (X n) μ := hsub.2.2
  have h_norm_bdd := submartingale_integral_norm_le hsub hbdd
  set B := (2 * C - ∫ ω, X 0 ω ∂μ).toNNReal
  have h_eLpNorm : ∀ n, eLpNorm (X n) 1 μ ≤ ↑B := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    rw [ENNReal.ofReal_le_coe]
    exact le_trans (h_norm_bdd n) (Real.le_coe_toNNReal _)
  have hconv := hsub.ae_tendsto_limitProcess h_eLpNorm
  have hasm : ∀ n, AEStronglyMeasurable (X n) μ :=
    fun n => (hsub.1 n).aestronglyMeasurable.mono (ℱ.le n)
  have hint_lim : Integrable (ℱ.limitProcess X μ) μ :=
    memLp_one_iff_integrable.mp (Filtration.memLp_limitProcess_of_eLpNorm_bdd hasm h_eLpNorm)
  exact ⟨ℱ.limitProcess X μ, hint_lim, hconv⟩


-- created on 2026-10-23
