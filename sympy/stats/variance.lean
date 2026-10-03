import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv

open MeasureTheory

/-!
[sympy.Variance / sympy.Covariance](https://github.com/sympy/sympy/blob/master/sympy/stats/symbolic_probability.py)
for real random variables, built on `Expectation.ofRV` (the `𝔼[x: π](…)` of `sympy.stats.joint_rv`)
with the `Expectation ℝ` (Bochner) instance. Only the weak `PSpace` is needed.
-/

/-- Two random variables with probability spaces span one jointly: the pair is a.e. measurable. -/
instance PSpace.joint
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {π : Measure Ω} {x : Ω → α} {y : Ω → β} [hx : PSpace π x] [hy : PSpace π y] :
    PSpace π (x, y) where
  toIsProbabilityMeasure := hx.toIsProbabilityMeasure
  aemeasurable := hx.aemeasurable.prodMk hy.aemeasurable

/-- Change of variables for the real expectation of an observable of `x`. -/
theorem Expectation.ofRV_eq_integral
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {π : Measure Ω} {x : Ω → α} [PSpace π x] {f : α → ℝ}
    (hf : AEStronglyMeasurable f (π.map x)) :
    Expectation.ofRV π x f = ∫ ω, f (x ω) ∂π := by
  simp only [Expectation.ofRV, expectation_real]
  exact integral_map PSpace.aemeasurable hf

/-- `𝔼[x: π](x) = ∫ x dπ`. -/
theorem Expectation.ofRV_self
    {Ω : Type*} [MeasurableSpace Ω] (π : Measure Ω) (x : Ω → ℝ) [PSpace π x] :
    Expectation.ofRV π x (fun a : ℝ ↦ a) = ∫ ω, x ω ∂π :=
  Expectation.ofRV_eq_integral measurable_id.aestronglyMeasurable

/-- [sympy.Variance]: `Var[x] = 𝔼[(x - 𝔼[x])²]`. -/
noncomputable def Variance
    {Ω : Type*} [MeasurableSpace Ω] (π : Measure Ω) (x : Ω → ℝ) [PSpace π x] : ℝ :=
  Expectation.ofRV π x (fun a : ℝ ↦ (a - Expectation.ofRV π x (fun a : ℝ ↦ a)) ^ 2)

/-- [sympy.Covariance]: `Cov[x, y] = 𝔼[(x - 𝔼[x]) (y - 𝔼[y])]`, over the joint law of `(x, y)`. -/
noncomputable def Covariance
    {Ω : Type*} [MeasurableSpace Ω] (π : Measure Ω) (x y : Ω → ℝ) [PSpace π x] [PSpace π y] : ℝ :=
  Expectation.ofRV π (x, y)
    (fun p : ℝ × ℝ ↦ (p.1 - Expectation.ofRV π x (fun a : ℝ ↦ a)) * (p.2 - Expectation.ofRV π y (fun a : ℝ ↦ a)))

theorem Variance.eq_integral
    {Ω : Type*} [MeasurableSpace Ω] {π : Measure Ω} {x : Ω → ℝ} [PSpace π x] :
    Variance π x = ∫ ω, (x ω - ∫ ω', x ω' ∂π) ^ 2 ∂π := by
  unfold Variance
  rw [Expectation.ofRV_self]
  exact Expectation.ofRV_eq_integral (Continuous.aestronglyMeasurable (by fun_prop))

theorem Covariance.eq_integral
    {Ω : Type*} [MeasurableSpace Ω] {π : Measure Ω} {x y : Ω → ℝ} [PSpace π x] [PSpace π y] :
    Covariance π x y = ∫ ω, (x ω - ∫ ω', x ω' ∂π) * (y ω - ∫ ω', y ω' ∂π) ∂π := by
  unfold Covariance
  rw [Expectation.ofRV_self, Expectation.ofRV_self]
  exact Expectation.ofRV_eq_integral (Continuous.aestronglyMeasurable (by fun_prop))
