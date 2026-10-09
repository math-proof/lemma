import sympy.physics.vector.kinematics
import sympy.Basic


/--
Position equals radial length times unit radial:
\(\vec{r}=r\,\hat{r}\) whenever \(\vec{r}\neq 0\).
-/
@[path]
private lemma main
  {d : ℕ}
  {r : Position d}
  {t : ℝ}
-- given
  (h : r t ≠ 0) :
-- imply
  r t = radial r t • unit_radial r t := by
-- proof
  simp only [radial, unit_radial]
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]


-- created on 2026-09-28
