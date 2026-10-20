import Mathlib
import sympy.Basic
import sympy.atlas.Probability.SkorokhodRepresentation
open MeasureTheory
open scoped ENNReal NNReal
open MathlibExt.Probability.SkorokhodRepresentationWanted


/--
[skorokhod_representation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/SkorokhodRepresentation.lean)
-/
@[path]
private lemma skorokhod_representation_eq
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : ℕ → ProbabilityMeasure X}
  {μ₀ : ProbabilityMeasure X}
-- given
  (hμ : Filter.Tendsto (fun n => μ n) Filter.atTop (nhds μ₀)) :
-- imply
  ∃ (Y : ℕ → ℝ → X) (Y₀ : ℝ → X),
    (∀ n, Measurable (Y n)) ∧ Measurable Y₀ ∧
    (∀ n, (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))).map (Y n) = (μ n : Measure X)) ∧
    (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))).map Y₀ = (μ₀ : Measure X) ∧
    ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))),
    Filter.Tendsto (fun n => Y n x) Filter.atTop (nhds (Y₀ x)) := by
-- proof
  apply MathlibExt.Probability.SkorokhodRepresentationWanted.skorokhod_representation μ μ₀ hμ


-- created on 2026-10-20
