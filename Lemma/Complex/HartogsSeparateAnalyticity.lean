import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.HartogsSeparateAnalyticity

open Complex.HartogsWanted
open MeasureTheory Set Metric Filter

/--
[hartogs_posLog_norm_le_circleAverage](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsSeparateAnalyticity.lean)
-/
@[path]
private lemma hartogs_posLog_norm_le_circleAverage_eq
-- given
  {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
  (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) :
-- imply
  Real.posLog ‖f c‖ ≤ Real.circleAverage (fun z ↦ Real.posLog ‖f z‖) c R := by
-- proof
  apply hartogs_posLog_norm_le_circleAverage hR hf

/--
[differentiableAt_uncurry_of_separately_differentiable_of_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsSeparateAnalyticity.lean)
-/
@[path]
private lemma differentiableAt_uncurry_of_separately_differentiable_of_bounded_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : E → ℂ → ℂ} {M : ℝ}
  (hf₁ : ∀ w, Differentiable ℂ (fun z ↦ f z w))
  (hf₂ : ∀ z, Differentiable ℂ (f z))
  (hM : ∀ z ∈ closedBall 0 1, ∀ w ∈ closedBall 0 1, ‖f z w‖ ≤ M) :
-- imply
  DifferentiableAt ℂ (Function.uncurry f) (0, 0) := by
-- proof
  apply differentiableAt_uncurry_of_separately_differentiable_of_bounded hf₁ hf₂ hM

/--
[differentiableAt_uncurry_of_separately_differentiable_of_locally_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsSeparateAnalyticity.lean)
-/
@[path]
private lemma differentiableAt_uncurry_of_separately_differentiable_of_locally_bounded_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : E → ℂ → ℂ} {U : Set E} {V : Set ℂ} {M : ℝ}
  {z₀ : E} {w₀ : ℂ}
  (hU : IsOpen U) (hV : IsOpen V)
  (hf₁ : ∀ w, Differentiable ℂ (fun z ↦ f z w))
  (hf₂ : ∀ z, Differentiable ℂ (f z))
  (hM : ∀ z ∈ U, ∀ w ∈ V, ‖f z w‖ ≤ M)
  (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ V) :
-- imply
  DifferentiableAt ℂ (Function.uncurry f) (z₀, w₀) := by
-- proof
  apply differentiableAt_uncurry_of_separately_differentiable_of_locally_bounded
    hU hV hf₁ hf₂ hM hz₀ hw₀

/--
[differentiableOn_cauchyCoefficient_of_separately_differentiable_of_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsSeparateAnalyticity.lean)
-/
@[path]
private lemma differentiableOn_cauchyCoefficient_of_separately_differentiable_of_bounded_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {f : E → ℂ → ℂ} {z₀ : E} {w₀ : ℂ} {A B M : ℝ}
  (hA : 0 < A) (hB : 0 < B)
  (hf₁ : ∀ w, Differentiable ℂ (fun z ↦ f z w))
  (hf₂ : ∀ z, Differentiable ℂ (f z))
  (hM : ∀ z ∈ closedBall z₀ A, ∀ w ∈ closedBall w₀ B, ‖f z w‖ ≤ M)
  (k : ℕ) :
-- imply
  DifferentiableOn ℂ
    (fun z ↦ (cauchyPowerSeries (f z) w₀ (B / 2) k) (fun _ ↦ 1))
    (ball z₀ (A / 2)) := by
-- proof
  apply differentiableOn_cauchyCoefficient_of_separately_differentiable_of_bounded
    hA hB hf₁ hf₂ hM k

/--
[norm_cauchyCoefficient_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsSeparateAnalyticity.lean)
-/
@[path]
private lemma norm_cauchyCoefficient_le_eq
-- given
  {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
  (hR : 0 < R) (hf : Differentiable ℂ f)
  (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (k : ℕ) :
-- imply
  ‖(cauchyPowerSeries f c R).coeff k‖ ≤ M * R⁻¹ ^ k := by
-- proof
  apply norm_cauchyCoefficient_le hR hf hM k

/--
[hartogsPolydisc_submean](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsSeparateAnalyticity.lean)
-/
@[path]
private lemma hartogsPolydisc_submean_eq
-- given
  {n : ℕ} {u : (Fin n → ℂ) → ℝ}
  {c : Fin n → ℂ} {R : ℝ}
  (hu : Continuous u) (hR : 0 < R)
  (hcircle : ∀ x ∈ closedBall c R, ∀ (i : Fin n) r, r ∈ Ioc 0 R →
    u x ≤ Real.circleAverage (fun z ↦ u (Function.update x i z)) (x i) r) :
-- imply
  (volume (closedBall (0 : ℂ) R)).toReal ^ n * u c ≤
    hartogsPolydiscIntegral u c R := by
-- proof
  apply hartogsPolydisc_submean hu hR hcircle

/--
[hartogs_eventually_uniform_of_submean](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsSeparateAnalyticity.lean)
-/
@[path]
private lemma hartogs_eventually_uniform_of_submean_eq
-- given
  {n : ℕ} {u : ℕ → (Fin n → ℂ) → ℝ}
  {c : Fin n → ℂ} {R C ε : ℝ}
  (hR : 0 < R)
  (hu : ∀ k, ContinuousOn (u k) (closedBall c R))
  (hu0 : ∀ k x, x ∈ closedBall c R → 0 ≤ u k x)
  (hC : 0 ≤ C)
  (hub : ∀ k x, x ∈ closedBall c R → u k x ≤ C)
  (hlim : ∀ x ∈ closedBall c R, Tendsto (fun k ↦ u k x) atTop (nhds 0))
  (hcircle : ∀ k x, x ∈ closedBall c R → ∀ (i : Fin n) r, 0 < r →
    (∀ z ∈ closedBall (x i) r,
      Function.update x i z ∈ closedBall c R) →
    u k x ≤ Real.circleAverage (fun z ↦ u k (Function.update x i z)) (x i) r)
  (hε : 0 < ε) :
-- imply
  ∀ᶠ k in atTop, ∀ x ∈ closedBall c (R / 4), u k x ≤ ε := by
-- proof
  apply hartogs_eventually_uniform_of_submean hR hu hu0 hC hub hlim hcircle hε

/--
[hartogs_separate_analyticity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HartogsSeparateAnalyticity.lean)
-/
@[path]
private lemma hartogs_separate_analyticity_eq
-- given
  {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
  (hf : ∀ (x : EuclideanSpace ℂ (Fin n)) (i : Fin n),
    Differentiable ℂ (fun z : ℂ =>
      f (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z)))) :
-- imply
  Differentiable ℂ f := by
-- proof
  apply hartogs_separate_analyticity hf


-- created on 2026-10-09
