import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.core.function

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

/-- [sympy.Variance]: `𝕍𝕒𝕣 π x = 𝔼[(x - 𝔼[x])²]`. -/
noncomputable def 𝕍𝕒𝕣
    {Ω : Type*} [MeasurableSpace Ω] (π : Measure Ω) (x : Ω → ℝ) [PSpace π x] : ℝ :=
  Expectation.ofRV π x (fun a : ℝ ↦ (a - Expectation.ofRV π x (fun a : ℝ ↦ a)) ^ 2)

/-- [sympy.Covariance]: `ℂ𝕠𝕧 π x y = 𝔼[(x - 𝔼[x]) (y - 𝔼[y])]`, over the joint law of `(x, y)`. -/
noncomputable def ℂ𝕠𝕧
    {Ω : Type*} [MeasurableSpace Ω] (π : Measure Ω) (x y : Ω → ℝ) [PSpace π x] [PSpace π y] : ℝ :=
  Expectation.ofRV π (x, y)
    (fun p : ℝ × ℝ ↦ (p.1 - Expectation.ofRV π x (fun a : ℝ ↦ a)) * (p.2 - Expectation.ofRV π y (fun a : ℝ ↦ a)))
