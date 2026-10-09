import Mathlib
import sympy.Basic
import sympy.Analysis.Convex.Choquet

open Convex.ChoquetWanted
open MeasureTheory Set

/-- [choquet_representation_of_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Choquet.lean) -/
@[path]
private lemma choquet_representation_of_isCompact_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {K : Set E} {x : E}
  (hKCompact : IsCompact K)
  (hx : x ∈ K) :
-- imply
  ∃ (μ : ProbabilityMeasure E),
    (μ : Measure E) (extremePoints ℝ K) = 1 ∧
      Integrable (fun y : E => y) (μ : Measure E) ∧
        integral (μ : Measure E) (fun y : E => y) = x := by
-- proof
  apply choquet_representation_of_isCompact hKCompact hx

/-- [choquet_representation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Choquet.lean) -/
@[path]
private lemma choquet_representation_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {K : Set E} {x : E}
  (hKCompact : IsCompact K)
  (hKConvex : Convex ℝ K)
  (hKNonempty : K.Nonempty)
  (hx : x ∈ K) :
-- imply
  ∃ (μ : ProbabilityMeasure E),
    (μ : Measure E) (extremePoints ℝ K) = 1 ∧
      Integrable (fun y : E => y) (μ : Measure E) ∧
        integral (μ : Measure E) (fun y : E => y) = x := by
-- proof
  apply choquet_representation hKCompact hKConvex hKNonempty hx

-- created on 2026-10-10
