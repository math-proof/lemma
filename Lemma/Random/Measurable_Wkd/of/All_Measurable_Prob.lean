import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Lemma.Random.MeasurableRkd
open MeasureTheory PolicyGradient Random


/--
If every `(x, u) ↦ π_θ(u | x)` is jointly measurable, so is the `k`-step expected reward
`x ↦ Wkd θ k x = 𝔼[r[t+k] | s[t] = x]`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (h : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (R : ℝ)
  (θ : Θ)
  (k : ℕ) :
-- imply
  Measurable (M.Wkd R θ k) := by
-- proof
  induction k with
  | zero =>
    exact (StronglyMeasurable.integral_prod_right' (ν := ReferenceMeasure.measure)
      (f := fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2 * M.rkd R z.1 z.2)
      ((h θ).mul (MeasurableRkd (M := M) R)).stronglyMeasurable).measurable
  | succ k ih =>
    apply (StronglyMeasurable.integral_prod_right' (ν := ReferenceMeasure.measure)
      (f := fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2 * ∫ y, M.Wkd R θ k y ∂(M.trans z))
      ((h θ).mul _).stronglyMeasurable).measurable
    apply (StronglyMeasurable.integral_kernel_prod_right' (κ := M.transK) (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.Wkd R θ k z.2)
      (ih.stronglyMeasurable.comp_measurable measurable_snd)).measurable


-- created on 2026-10-07
-- updated on 2026-11-18
