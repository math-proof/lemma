import Mathlib
import sympy.Basic
import sympy.atlas.Probability.LevyContinuity
open MeasureTheory Filter Topology
open MathlibExt.Probability.LevyContinuityWanted


/--
[levy_continuity_of_charFun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyContinuity.lean)
-/
@[path]
private lemma levy_continuity_of_charFun_eq
  {d : ℕ}
  {μn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
  {φ : EuclideanSpace ℝ (Fin d) → ℂ}
-- given
  (hφ : ∀ t, Tendsto (fun n => charFun (μn n : Measure _) t) atTop (nhds (φ t)))
  (hcont : ContinuousAt φ (0 : EuclideanSpace ℝ (Fin d))) :
-- imply
  ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      (∀ t, φ t = charFun (μ : Measure _) t) ∧
      Tendsto (fun n => μn n) atTop (nhds μ) := by
-- proof
  apply MathlibExt.Probability.LevyContinuityWanted.levy_continuity_of_charFun hφ hcont


-- created on 2026-10-20
