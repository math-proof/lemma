import Def.Analysis.SpecialFunctions.TensorFunctions
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Nat Random Real


/--
`∫ z, (if s(z) = y then 1 else 0) * g z ∂(stageK θ y') = δ_{y' y} * ∫ z, g z ∂(stageK θ y')`
for the continuous-action stage kernel (`DensityModel`).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [DecidableEq S]
  {M : DensityModel Θ S A}
  {g : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (hg : StronglyMeasurable g)
  (hC : ∀ z, ‖g z‖ ≤ C)
  (θ : Θ)
  (y y' : S) :
-- imply
  ∫ z, (if z.2.1 = y then (1:ℝ) else 0) * g z ∂(M.stageK θ y') =
    (KroneckerDelta y' y : ℝ) * ∫ z, g z ∂(M.stageK θ y') := by
-- proof
  have hm : StronglyMeasurable (fun z : ℝ × S × A => (if z.2.1 = y then (1:ℝ) else 0) * g z) :=
    (StronglyMeasurable_Eq12 y).mul hg
  rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity (M := M) hm
    (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × S × A => z.2.1 = y)) hC) θ,
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity (M := M) hg hC θ]
  by_cases h : y' = y <;> simp [h, KroneckerDelta]


-- created on 2026-11-04
