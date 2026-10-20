import Mathlib
import sympy.Basic
import sympy.atlas.Probability.LevyKhintchin
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology
open MetaMathlibExt


/--
[levy_Khintchin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma levy_Khintchin_eq
  :
-- imply
  ∀ (μ : MeasureTheory.Measure ℝ), MeasureTheory.IsProbabilityMeasure μ →
    ((∀ n : ℕ, n ≠ 0 →
    ∃ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν ∧
    μ = Nat.iterate (MeasureTheory.Measure.conv ν) (n - 1) ν) ↔
    ∃ γ : ℝ, ∃ σ : ℝ, 0 ≤ σ ∧
    ∃ ν : MeasureTheory.Measure ℝ,
    ν {0} = 0 ∧ (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) ∧
    ∀ t : ℝ, MeasureTheory.charFun μ t =
    Complex.exp ((Complex.I * (γ : ℂ) * (t : ℂ) -
    (((σ ^ 2 * t ^ 2 : ℝ) : ℂ) / 2) +
    ∫ x, (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 -
    Set.indicator {y : ℝ | |y| ≤ 1}
    (fun y => Complex.I * (t : ℂ) * (y : ℂ)) x) ∂ν))) := by
-- proof
  apply MetaMathlibExt.levy_Khintchin


-- created on 2026-10-20
