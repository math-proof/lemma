import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorem.Probability.CondExpectation
import Theorem.Probability.JointRv.AsRV
open MeasureTheory ProbabilityTheory


/--
Law of total expectation, also called the law of iterated expectations, for a
random variable `X` with countably many values:
`𝔼[𝔼[Y | X]] = 𝔼[Y]`. The inner expectation is `𝔼[Y | X = «\sf{X}»]`, and the outer one
sums those values against `ℙ(X = «\sf{X}»)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  {π : Measure Ω} [IsFiniteMeasure π] {X : Ω → α} [PSpace π X]
  {Y : Ω → ℝ} [PSpace π Y]
-- given
  (hX : Measurable X)
  (hY : Integrable Y π) :
-- imply
  𝔼[X: π](𝔼[Y: π](Y | X)) = 𝔼[Y: π](Y) := by
-- proof
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_real]
  have hYae : AEMeasurable Y π := PSpace.aemeasurable (x := Y)
  have hmapY : ∫ a, a ∂(π.map Y) = ∫ ω, Y ω ∂π :=
    integral_map hYae measurable_id.aestronglyMeasurable
  rw [hmapY]
  have hae :
      (fun ω ↦ Expectation.condEval π Y X id (X ω)) =ᵐ[π]
        Expectation.condSigma π Y X id :=
    Expectation.condEval_comp_ae_eq_condSigma hYae hX stronglyMeasurable_id hY
  have hsm : AEStronglyMeasurable (fun x => Expectation.condEval π Y X id x) (π.map X) :=
    (StronglyMeasurable.of_discrete
      (f := fun x => Expectation.condEval π Y X id x)).aestronglyMeasurable
  have hmapX :
      ∫ x, Expectation.condEval π Y X id x ∂(π.map X) =
        ∫ ω, Expectation.condEval π Y X id (X ω) ∂π :=
    (integral_map (μ := π) (f := X) hX.aemeasurable hsm).symm
  rw [hmapX, integral_congr_ae hae]
  simp only [Expectation.condSigma]
  exact integral_condExp (μ := π) hY


-- created on 2023-03-31
-- updated on 2026-11-13
