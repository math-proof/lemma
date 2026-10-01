import Lemma.Real.Inner_PolarRadial_PolarAngular.eq.Zero
import Lemma.Real.NormPolarAngular.eq.One
import Lemma.Real.NormPolarRadial.eq.One
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Polar orthonormal expansion uniqueness:
\(a\,\hat{r}+b\,\hat{\theta}=c\,\hat{r}\) implies \(a=c\) and \(b=0\).
-/
@[main]
private lemma main
  {θ a b c : ℝ}
-- given
  (h : a • polar_radial θ + b • polar_angular θ = c • polar_radial θ) :
-- imply
  a = c ∧ b = 0 := by
-- proof
  have hr1 : ‖polar_radial θ‖ = 1 := Real.NormPolarRadial.eq.One θ
  have hθ1 : ‖polar_angular θ‖ = 1 := Real.NormPolarAngular.eq.One θ
  have horth : inner ℝ (polar_radial θ) (polar_angular θ) = 0 :=
    Real.Inner_PolarRadial_PolarAngular.eq.Zero θ
  constructor
  · -- take inner product with r̂
    have hinner := congrArg (fun v => inner ℝ (polar_radial θ) v) h
    have hL :
        inner ℝ (polar_radial θ) (a • polar_radial θ + b • polar_angular θ) = a := by
      simp [inner_add_right, real_inner_smul_right, hr1, horth]
    have hR :
        inner ℝ (polar_radial θ) (c • polar_radial θ) = c := by
      simp [real_inner_smul_right, hr1]
    exact hL.symm.trans (hinner.trans hR)
  · -- take inner product with θ̂
    have hinner := congrArg (fun v => inner ℝ (polar_angular θ) v) h
    have horth' : inner ℝ (polar_angular θ) (polar_radial θ) = 0 := by
      rw [real_inner_comm]; exact horth
    have hL :
        inner ℝ (polar_angular θ) (a • polar_radial θ + b • polar_angular θ) = b := by
      simp [inner_add_right, real_inner_smul_right, hθ1, horth']
    have hR :
        inner ℝ (polar_angular θ) (c • polar_radial θ) = 0 := by
      simp [real_inner_smul_right, horth']
    exact hL.symm.trans (hinner.trans hR)


-- created on 2026-09-28
