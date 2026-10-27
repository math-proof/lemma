import Mathlib.Probability.Independence.Integration
import Syntax.Probability.JointRv.Part6
import Theorem.Function
import Instance.Probability.Moments.Variance
open MeasureTheory


/-- [sympy.Variance]: `𝕍𝕒𝕣 π x = 𝔼[(x - 𝔼[x])²]`. -/
noncomputable def 𝕍𝕒𝕣
    {Ω : Type*} [MeasurableSpace Ω] (π : Measure Ω) (x : Ω → ℝ) [PSpace π x] : ℝ :=
  Expectation.ofRV π x (fun a : ℝ ↦ (a - Expectation.ofRV π x (fun a : ℝ ↦ a)) ^ 2)

/-- [sympy.Covariance]: `ℂ𝕠𝕧 π x y = 𝔼[(x - 𝔼[x]) (y - 𝔼[y])]`, over the joint law of `(x, y)`. -/
noncomputable def ℂ𝕠𝕧
    {Ω : Type*} [MeasurableSpace Ω] (π : Measure Ω) (x y : Ω → ℝ) [PSpace π x] [PSpace π y] : ℝ :=
  Expectation.ofRV π (x, y)
    (fun p : ℝ × ℝ ↦ (p.1 - Expectation.ofRV π x (fun a : ℝ ↦ a)) * (p.2 - Expectation.ofRV π y (fun a : ℝ ↦ a)))

