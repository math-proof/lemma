import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.StrassenFinite.Part2
open Finset StatMech StatMech.Probability


/--
[StochasticDom.of_isMonotoneCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/StrassenFinite.lean)
-/
@[path]
private lemma of_isMonotoneCoupling_eq
  [Fintype P]
  [PartialOrder P]
  [DecidableEq P]
  {μ ν : P → ℝ≥0}
  {π : P × P → ℝ≥0}
-- given
  (h : IsMonotoneCoupling μ ν π) :
-- imply
  StochasticDom μ ν := by
-- proof
  apply StatMech.Probability.StochasticDom.of_isMonotoneCoupling h

/--
[exists_isMonotoneCoupling_of_stochasticDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/StrassenFinite.lean)
-/
@[path]
private lemma exists_isMonotoneCoupling_of_stochasticDom_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  {μ ν : P → ℝ≥0}
-- given
  (hTOT : ∑ x, μ x = ∑ x, ν x)
  (hSD : StochasticDom μ ν) :
-- imply
  ∃ π : P × P → ℝ≥0, IsMonotoneCoupling μ ν π := by
-- proof
  apply StatMech.Probability.exists_isMonotoneCoupling_of_stochasticDom hTOT hSD

/--
[strassen_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/StrassenFinite.lean)
-/
@[path]
private lemma strassen_finite_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  {μ ν : P → ℝ≥0}
-- given
  (hTOT : ∑ x, μ x = ∑ x, ν x) :
-- imply
  StochasticDom μ ν ↔ ∃ π : P × P → ℝ≥0, IsMonotoneCoupling μ ν π := by
-- proof
  apply StatMech.Probability.strassen_finite hTOT


-- created on 2026-10-23
