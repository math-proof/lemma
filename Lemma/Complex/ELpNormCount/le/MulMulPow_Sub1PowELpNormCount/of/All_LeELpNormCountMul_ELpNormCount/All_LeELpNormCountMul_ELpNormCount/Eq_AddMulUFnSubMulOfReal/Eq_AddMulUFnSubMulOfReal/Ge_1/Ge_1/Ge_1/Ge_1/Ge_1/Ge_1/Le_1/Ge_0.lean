import Mathlib
import sympy.Basic
import sympy.calculus.functional_analysis.RieszThorin

open MeasureTheory
open scoped ENNReal

/--
[RieszThorin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RieszThorin.lean)
-/
@[path]
private lemma riesz_thorin_finite_le
-- given
  {ι κ : Type*} [Finite ι] [Finite κ]
  [MeasurableSpace ι] [MeasurableSpace κ]
  [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
  {p₀ p₁ q₀ q₁ p q : ENNReal}
  {θ : ℝ}
  {M₀ M₁ : ENNReal}
  (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
  (hθ₀ : 0 ≤ θ)
  (hθ₁ : θ ≤ 1)
  (hp₀ : 1 ≤ p₀)
  (hp₁ : 1 ≤ p₁)
  (hp : 1 ≤ p)
  (hq₀ : 1 ≤ q₀)
  (hq₁ : 1 ≤ q₁)
  (hq : 1 ≤ q)
  (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
  (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
  (h₀ : ∀ f : ι → Complex, eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤ M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
  (h₁ : ∀ f : ι → Complex, eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤ M₁ * eLpNorm f p₁ (Measure.count : Measure ι))
  (f : ι → Complex) :
-- imply
  eLpNorm (T f) q (Measure.count : Measure κ) ≤ (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p (Measure.count : Measure ι) := by
-- proof
  apply FunctionalAnalysis.RieszThorinWanted.riesz_thorin_finite hθ₀ hθ₁ hp₀ hp₁ hp hq₀ hq₁ hq hp_eq hq_eq T h₀ h₁

/--
[RieszThorin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RieszThorin.lean)
-/
@[path]
private lemma riesz_thorin_le
-- given
  {ι κ : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSpace κ]
  [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
  {p₀ p₁ q₀ q₁ p q : ENNReal}
  {θ : ℝ}
  {M₀ M₁ : ENNReal}
  (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
  (hθ₀ : 0 ≤ θ)
  (hθ₁ : θ ≤ 1)
  (hp₀ : 1 ≤ p₀)
  (hp₁ : 1 ≤ p₁)
  (hp : 1 ≤ p)
  (hq₀ : 1 ≤ q₀)
  (hq₁ : 1 ≤ q₁)
  (hq : 1 ≤ q)
  (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
  (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
  (h₀ : ∀ f : ι → Complex, eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤ M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
  (h₁ : ∀ f : ι → Complex, eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤ M₁ * eLpNorm f p₁ (Measure.count : Measure ι))
  (f : ι → Complex) :
-- imply
  eLpNorm (T f) q (Measure.count : Measure κ) ≤ (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p (Measure.count : Measure ι) := by
-- proof
  apply FunctionalAnalysis.RieszThorinWanted.riesz_thorin hθ₀ hθ₁ hp₀ hp₁ hp hq₀ hq₁ hq hp_eq hq_eq T h₀ h₁

-- created on 2026-10-10
