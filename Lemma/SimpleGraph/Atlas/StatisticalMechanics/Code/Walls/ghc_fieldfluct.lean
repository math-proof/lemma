import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.ghc_fieldfluct
open Finset StatMech StatMech.Walls


/--
[totalSpinM_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldfluct.lean)
-/
@[path]
private lemma totalSpinM_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V} :
-- imply
  totalSpinM s = totalSpin s := by
-- proof
  apply StatMech.Walls.totalSpinM_eq G s

/--
[ghc_field_fluctuation_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldfluct.lean)
-/
@[path]
private lemma ghc_field_fluctuation_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => isingExpectation G β h f) (β * (isingExpectation G β h (fun s => f s * totalSpinM s) - isingExpectation G β h f * isingExpectation G β h totalSpinM)) h := by
-- proof
  apply StatMech.Walls.ghc_field_fluctuation_hasDerivAt G β h f

/--
[ghc_field_fluctuation_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldfluct.lean)
-/
@[path]
private lemma ghc_field_fluctuation_deriv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  deriv (fun h => isingExpectation G β h f) h = β * (isingExpectation G β h (fun s => f s * totalSpinM s) - isingExpectation G β h f * isingExpectation G β h totalSpinM) := by
-- proof
  apply StatMech.Walls.ghc_field_fluctuation_deriv G β h f

/--
[ghc_field_fluctuation_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldfluct.lean)
-/
@[path]
private lemma ghc_field_fluctuation_differentiableAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  DifferentiableAt ℝ (fun h => isingExpectation G β h f) h := by
-- proof
  apply StatMech.Walls.ghc_field_fluctuation_differentiableAt G β h f

/--
[ghc_susceptibility_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldfluct.lean)
-/
@[path]
private lemma ghc_susceptibility_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => isingExpectation G β h (fun s => spin s o)) (β * (isingExpectation G β h (fun s => spin s o * totalSpinM s) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h totalSpinM)) h := by
-- proof
  apply StatMech.Walls.ghc_susceptibility_hasDerivAt G β h o

/--
[ghc_susceptibility_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_fieldfluct.lean)
-/
@[path]
private lemma ghc_susceptibility_deriv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  deriv (fun h => isingExpectation G β h (fun s => spin s o)) h = β * (isingExpectation G β h (fun s => spin s o * totalSpinM s) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h totalSpinM) := by
-- proof
  apply StatMech.Walls.ghc_susceptibility_deriv G β h o


-- created on 2026-10-23
