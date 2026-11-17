module

public import Theorem.Random.KlDiv.eq.F
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

public section

open BoundedContinuousFunction ENNReal InformationTheory MeasureTheory Random Real


/--
The Kullback–Leibler divergence is lower semicontinuous for the topology of weak convergence.
Each bounded continuous test function gives a continuous function of the probability, and the
divergence is the supremum of the corresponding extended-real expressions.
-/
public theorem Random.LowerSemicontinuous_KlDivMeasure
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ] :
-- imply
  LowerSemicontinuous fun ν : ProbabilityMeasure α => klDiv (ν : Measure α) μ :=
-- proof
by
  have hI : (fun ν : ProbabilityMeasure α => klDiv (ν : Measure α) μ) =
      (fun ν : ProbabilityMeasure α => ⨆ f : BoundedContinuousFunction α ℝ, ENNReal.ofReal
        (∫ x, f x ∂(ν : Measure α) - log (∫ x, exp (f x) ∂μ))) := by
    ext ν
    exact KlDiv.eq.F
  rw [hI]
  refine lowerSemicontinuous_iSup fun f => ?_
  exact (continuous_ofReal.comp
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).sub
      continuous_const)).lowerSemicontinuous


-- created on 2026-11-02
