import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
import Lemma.Random.Cov.eq.Integral
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x y z : Ω → ℝ}
  [PSpace π x]
  [PSpace π y]
  [PSpace π z]
  [PSpace π (y + z)]
-- given
  (hx : Integrable x π)
  (hy : Integrable y π)
  (hz : Integrable z π)
  (hxy : Integrable (fun ω => x ω * y ω) π)
  (hxz : Integrable (fun ω => x ω * z ω) π) :
-- imply
  Covariance π x (y + z) = Covariance π x y + Covariance π x z := by
-- proof
  have hE : ∫ ω, (y + z) ω ∂π = ∫ ω, y ω ∂π + ∫ ω, z ω ∂π := integral_add hy hz
  have hL : Integrable (fun ω => (x ω - ∫ ω', x ω' ∂π) * (y ω - ∫ ω', y ω' ∂π)) π := by
    have h₀ := (hxy.sub ((hx.const_mul (∫ ω', y ω' ∂π)).add
      (hy.const_mul (∫ ω', x ω' ∂π)))).add (integrable_const ((∫ ω', x ω' ∂π) * ∫ ω', y ω' ∂π))
    have hf : ∀ ω, x ω * y ω - ((∫ ω', y ω' ∂π) * x ω + (∫ ω', x ω' ∂π) * y ω) +
        (∫ ω', x ω' ∂π) * ∫ ω', y ω' ∂π =
        (x ω - ∫ ω', x ω' ∂π) * (y ω - ∫ ω', y ω' ∂π) := fun ω => by ring
    exact (integrable_congr (Filter.Eventually.of_forall hf)).mp h₀
  have hR : Integrable (fun ω => (x ω - ∫ ω', x ω' ∂π) * (z ω - ∫ ω', z ω' ∂π)) π := by
    have h₀ := (hxz.sub ((hx.const_mul (∫ ω', z ω' ∂π)).add
      (hz.const_mul (∫ ω', x ω' ∂π)))).add (integrable_const ((∫ ω', x ω' ∂π) * ∫ ω', z ω' ∂π))
    have hf : ∀ ω, x ω * z ω - ((∫ ω', z ω' ∂π) * x ω + (∫ ω', x ω' ∂π) * z ω) +
        (∫ ω', x ω' ∂π) * ∫ ω', z ω' ∂π =
        (x ω - ∫ ω', x ω' ∂π) * (z ω - ∫ ω', z ω' ∂π) := fun ω => by ring
    exact (integrable_congr (Filter.Eventually.of_forall hf)).mp h₀
  have e : ∀ ω, (x ω - ∫ ω', x ω' ∂π) * ((y + z) ω - (∫ ω', y ω' ∂π + ∫ ω', z ω' ∂π)) =
      (x ω - ∫ ω', x ω' ∂π) * (y ω - ∫ ω', y ω' ∂π) +
        (x ω - ∫ ω', x ω' ∂π) * (z ω - ∫ ω', z ω' ∂π) := fun ω => by
    rw [Pi.add_apply]
    ring
  rw [Random.Cov.eq.Integral, Random.Cov.eq.Integral, Random.Cov.eq.Integral, hE]
  simp only [e]
  rw [integral_add hL hR]


-- created on 2023-04-19
