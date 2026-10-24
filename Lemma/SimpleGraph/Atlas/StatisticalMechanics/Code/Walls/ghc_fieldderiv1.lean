import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.ghc_fieldderiv1
open Finset SimpleGraph StatMech StatMech.Walls


/--
[ghc_hasDerivAt_magnetization_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldderiv1.lean)
-/
@[path]
private lemma ghc_hasDerivAt_magnetization_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => isingExpectation G β h (fun s => spin s o)) (β * (isingExpectation G β h (fun s => spin s o * totalSpin s) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h totalSpin)) h := by
-- proof
  apply StatMech.Walls.ghc_hasDerivAt_magnetization_field G β h o

/--
[ghc_susceptibility_eq_sum_cov2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldderiv1.lean)
-/
@[path]
private lemma ghc_susceptibility_eq_sum_cov2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  susceptibility G β h o = ∑ x, cov2 G β h o x := by
-- proof
  apply StatMech.Walls.ghc_susceptibility_eq_sum_cov2 G β h o

/--
[ghc_cov_summand_eq_cov2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldderiv1.lean)
-/
@[path]
private lemma ghc_cov_summand_eq_cov2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => spin s o * spin s x) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x) = cov2 G β h o x := by
-- proof
  apply StatMech.Walls.ghc_cov_summand_eq_cov2 G β h o x

/--
[ghc_field_deriv1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldderiv1.lean)
-/
@[path]
private lemma ghc_field_deriv1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  deriv (fun h => isingExpectation G β h (fun s => spin s o)) h = β * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.ghc_field_deriv1 G β h o

/--
[ghc_field_deriv1_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldderiv1.lean)
-/
@[path]
private lemma ghc_field_deriv1_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  deriv (fun h => isingExpectation G β h (fun s => spin s o)) h = β * ∑ x, cov2 G β h o x := by
-- proof
  apply StatMech.Walls.ghc_field_deriv1_sum G β h o

/--
[ghc_field_deriv1_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldderiv1.lean)
-/
@[path]
private lemma ghc_field_deriv1_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => isingExpectation G β h (fun s => spin s o)) (β * susceptibility G β h o) h := by
-- proof
  apply StatMech.Walls.ghc_field_deriv1_hasDerivAt G β h o

/--
[ghc_field_deriv1_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldderiv1.lean)
-/
@[path]
private lemma ghc_field_deriv1_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ deriv (fun h => isingExpectation G β h (fun s => spin s o)) h := by
-- proof
  apply StatMech.Walls.ghc_field_deriv1_nonneg G β h hβ hh o


-- created on 2026-10-23
