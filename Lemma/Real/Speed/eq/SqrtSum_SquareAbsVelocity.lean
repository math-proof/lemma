import Lemma.Real.Norm.eq.Sqrt
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Speed is the Euclidean norm of velocity:
\(v=|\vec{v}|=\sqrt{\sum_i v_i^2}\).
-/
@[main]
private lemma main
  {d : ℕ}
  (r : Position d)
  (t : ℝ) :
-- imply
  speed r t = √(∑ i, |velocity r t i| ^ 2) := by
-- proof
  simpa [speed] using Real.Norm.eq.Sqrt (x := velocity r t)


-- created on 2026-09-28
