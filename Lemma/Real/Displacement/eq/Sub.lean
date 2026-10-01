import sympy.physics.vector.kinematics
import sympy.Basic


/--
Displacement is the difference of positions:
\(\Delta\vec{r}=\vec{r}(t+\Delta t)-\vec{r}(t)\).
-/
@[main]
private lemma main
  {d : ℕ}
  (r : Position d)
  (t Δt : ℝ) :
-- imply
  displacement r t Δt = r (t + Δt) - r t := by
-- proof
  rfl


-- created on 2026-09-28
