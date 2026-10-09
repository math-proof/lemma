import Mathlib.Analysis.Calculus.Deriv.Basic
import sympy.physics.vector.kinematics
import sympy.Basic


/--
If \(\vec{r}\) is differentiable at \(t\) with derivative \(\vec{v}\), then
the kinematic velocity equals \(\vec{v}\).
-/
@[path]
private lemma main
  {d : ℕ}
  {r : Position d}
  {v : EuclideanVec d}
  {t : ℝ}
-- given
  (h : HasDerivAt r v t) :
-- imply
  velocity r t = v := by
-- proof
  simpa [velocity] using h.deriv


-- created on 2026-09-28
