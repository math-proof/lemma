import Lemma.Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1
import Lemma.Real.IntegralArealSpeed.eq.IntegralDivSquare.of.Ne_0.All_DifferentiableAt.ContinuousOn.Continuous.All_Eq
import Lemma.Real.IntegralDivSquare.eq.MulMul.of.Gt_Neg1.Lt_1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import sympy.physics.vector.kinematics
import sympy.Basic
open Real


/--
Kepler's area law closes up on the ellipse: if the radius follows
\(r(\varphi)=\dfrac{p}{1-e\cos\varphi}\) (\(|e|<1\)) and the polar angle advances by \(2\pi\)
over \([0,T]\), then the swept area is the ellipse area \(\pi ab\), where
\(a=\dfrac{p}{1-e^2}\) and \(b=a\sqrt{1-e^2}\).
-/
@[main]
private lemma main
  {m e p T : ℝ}
  {r ρ θ : ℝ → ℝ}
-- given
  (hm : m ≠ 0)
  (he₀ : -1 < e)
  (he₁ : e < 1)
  (hθ : ∀ t ∈ Set.uIcc 0 T, DifferentiableAt ℝ θ t)
  (hθ' : ContinuousOn (deriv θ) (Set.uIcc 0 T))
  (hθT : θ T = θ 0 + 2 * π)
  (hr : ∀ φ, r φ = p / (1 - e * Real.cos φ))
  (hρ : ∀ t, ρ t = r (θ t)) :
-- imply
  ∫ t in (0 : ℝ)..T, areal_speed m ρ θ t =
    π * (p / (1 - e ^ 2)) * (p / (1 - e ^ 2) * Real.sqrt (1 - e ^ 2)) := by
-- proof
  have hrc : Continuous r := by
    have : r = fun φ => p / (1 - e * Real.cos φ) := funext hr
    rw [this]
    refine Continuous.div continuous_const (by fun_prop) fun x => ?_
    exact (Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1 he₀ he₁ x).ne'
  rw [Real.IntegralArealSpeed.eq.IntegralDivSquare.of.Ne_0.All_DifferentiableAt.ContinuousOn.Continuous.All_Eq
    hm hθ hθ' hrc hρ, hθT]
  have hper : Function.Periodic (fun φ => (r φ) ^ 2 / 2) (2 * π) := by
    intro x
    simp only [hr, Real.cos_add_two_pi]
  rw [hper.intervalIntegral_add_eq (θ 0) 0, zero_add]
  simp only [hr]
  exact Real.IntegralDivSquare.eq.MulMul.of.Gt_Neg1.Lt_1 he₀ he₁


-- created on 2026-09-29