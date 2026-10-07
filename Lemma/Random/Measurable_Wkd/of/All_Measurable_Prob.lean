import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Lemma.Random.MeasurableRkd
open MeasureTheory PolicyGradient Random


/--
If every `(x, u) ↦ π_θ(u | x)` is jointly measurable, so is the `k`-step expected reward
`x ↦ Wkd θ k x = 𝔼[r[t+k] | s[t] = x]`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
-- given
  (h : ∀ θ, Measurable (fun z : S × A => M.pol.prob θ z.1 z.2))
  (θ : Θ)
  (k : ℕ) :
-- imply
  Measurable (M.Wkd θ k) := by
-- proof
  induction k with
  | zero =>
    exact (StronglyMeasurable.integral_prod_right' (ν := (ReferenceMeasure.measure : Measure A))
      (f := fun z : S × A => M.pol.prob θ z.1 z.2 * M.rkd z.1 z.2)
      ((h θ).mul (MeasurableRkd (M := M))).stronglyMeasurable).measurable
  | succ k ih =>
    have := M.env.trans_markov
    apply (StronglyMeasurable.integral_prod_right' (ν := (ReferenceMeasure.measure : Measure A))
      (f := fun z : S × A => M.pol.prob θ z.1 z.2 * ∫ y, M.Wkd θ k y ∂(M.env.trans z))
      ((h θ).mul _).stronglyMeasurable).measurable
    apply (StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans) (f := fun z : (S × A) × S => M.Wkd θ k z.2)
      (ih.stronglyMeasurable.comp_measurable measurable_snd)).measurable


-- created on 2026-10-07
