import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import sympy.Basic


@[path]
private lemma main
  {f h : ℝ → ℝ} {a h' x : ℝ}
  (h₀ : Continuous f)
  (h₁ : HasDerivAt h h' x) :
-- imply
  deriv (fun y => ∫ t in a..h y, f t) x = f (h x) * h' := by
-- proof
  have hF : HasDerivAt (fun u => ∫ t in a..u, f t) (f (h x)) (h x) :=
    (h₀.integral_hasStrictDerivAt a (h x)).hasDerivAt
  have hfun : (fun y => ∫ t in a..h y, f t) =ᶠ[nhds x]
      ((fun u => ∫ t in a..u, f t) ∘ h) := by
    filter_upwards with y
    rfl
  rw [((hF.comp x h₁).congr_of_eventuallyEq hfun).deriv]


-- created on 2026-10-11
-- updated on 2026-10-17
