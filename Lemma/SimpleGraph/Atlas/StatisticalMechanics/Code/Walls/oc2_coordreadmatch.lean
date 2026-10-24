import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc2_coordreadmatch
open Finset StatMech StatMech.Walls


/--
[oc2_coord_eq_coordI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_coordreadmatch.lean)
-/
@[path]
private lemma oc2_coord_eq_coordI_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  OSSS.Lindeberg.coord e ω = CovLowerBound.coordI e ω := by
-- proof
  apply StatMech.Walls.oc2_coord_eq_coordI e ω

/--
[oc2_coord_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_coordreadmatch.lean)
-/
@[path]
private lemma oc2_coord_eq_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  OSSS.Lindeberg.coord e ω = (if ω e = true then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Walls.oc2_coord_eq_indicator e ω

/--
[oc2_coordI_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_coordreadmatch.lean)
-/
@[path]
private lemma oc2_coordI_eq_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  CovLowerBound.coordI e ω = (if ω e = true then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Walls.oc2_coordI_eq_indicator e ω

/--
[oc2_coord_read_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_coordreadmatch.lean)
-/
@[path]
private lemma oc2_coord_read_match_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u : Fin n → ℝ}
  {e : E} :
-- imply
  OSSS.Lindeberg.coord e (OSSS.Coding.codeMap μ σ u) = CovLowerBound.coordI e (OSSS.Coding.codeMap μ σ u) ∧ OSSS.Lindeberg.coord e (OSSS.Coding.codeMap μ σ u) = (if (OSSS.Coding.codeMap μ σ u) e = true then (1 : ℝ) else 0) ∧ CovLowerBound.coordI e (OSSS.Coding.codeMap μ σ u) = (if (OSSS.Coding.codeMap μ σ u) e = true then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Walls.oc2_coord_read_match μ σ u e

/--
[oc2_coord_read_match_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_coordreadmatch.lean)
-/
@[path]
private lemma oc2_coord_read_match_sum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u : Fin n → ℝ} :
-- imply
  (∑ e, OSSS.Lindeberg.coord e (OSSS.Coding.codeMap μ σ u)) = ∑ e, CovLowerBound.coordI e (OSSS.Coding.codeMap μ σ u) := by
-- proof
  apply StatMech.Walls.oc2_coord_read_match_sum μ σ u


-- created on 2026-10-23
