import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Velocity as the limit of average displacement:
\(\vec{v}(t)=\lim_{\Delta t\to 0}\Delta\vec{r}/\Delta t\).
-/
@[main]
private lemma main
  {d : ℕ}
  {r : Position d}
  {v : EuclideanVec d}
  {t : ℝ}
-- given
  (h : HasDerivAt r v t) :
-- imply
  Filter.Tendsto (fun Δt : ℝ => (Δt)⁻¹ • displacement r t Δt) (nhdsWithin 0 {0}ᶜ) (nhds v) := by
-- proof
  simpa [displacement] using h.tendsto_slope_zero


-- created on 2026-09-28
