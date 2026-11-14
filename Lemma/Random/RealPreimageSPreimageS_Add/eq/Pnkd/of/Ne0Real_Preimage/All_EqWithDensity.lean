import Lemma.Real.Norm_Eq12.le.One
import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Pnkd.eq.Integral
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Real


private lemma real_inter
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [ReferenceMeasure 𝒜]
  [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t t' : ℕ)
  (x y : 𝒮) :
-- imply
  (M θ).real (s t ⁻¹' {x} ∩ s t' ⁻¹' {y}) =
    ∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s t' ω = y then (1:ℝ) else 0) ∂(M θ) := by
-- proof
  rw [← integral_indicator_one ((Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton x)).inter
    (Random.Measurable.of.All_Eq.snd.fst h₀ t' (measurableSet_singleton y)))]
  congr 1
  funext ω
  if h1 : s t ω = x then
    if h2 : s t' ω = y then
      simp [Set.indicator, h1, h2]
    else
      simp [Set.indicator, h1, h2]
  else
    if h2 : s t' ω = y then
      simp [Set.indicator, h1, h2]
    else
      simp [Set.indicator, h1, h2]

/--
On a reachable state (`ℙ(s[t] = x) ≠ 0`), `ℙ(s[t+n] = y | s[t] = x) = Pnkd θ n x y`
(time-homogeneous `n`-step transition of a `DensityModel`).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (n : ℕ)
  (y : 𝒮) :
-- imply
  (M θ)[|s t ⁻¹' {x}].real (s (t + n) ⁻¹' {y}) = M.Pnkd θ n x y := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  have hInt :
    ∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s (t + n) ω = y then (1:ℝ) else 0) ∂(M θ) =
      (M θ).real (s t ⁻¹' {x}) * M.Pnkd θ n x y :=
    (Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity h₀ (M := M)
      (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) θ t n x).trans
      (by rw [← Pnkd.eq.Integral (M := M) θ n x y])
  rw [measureReal_def, cond_apply (Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton x)),
    ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, real_inter h₀, hInt,
    inv_mul_cancel_left₀ h₁]


-- created on 2026-11-13
