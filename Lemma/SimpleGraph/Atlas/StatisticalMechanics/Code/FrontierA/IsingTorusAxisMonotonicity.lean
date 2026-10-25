import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusAxisMonotonicity
open Finset Set StatMech StatMech.FrontierA


/--
[isingTorusAxisCorrelation_logConvex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisMonotonicity.lean)
-/
@[path]
private lemma isingTorusAxisCorrelation_logConvex_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 ≤ beta)
  (hn2 : 2 ≤ n)
  (hnH : n ≤ 2 ^ (k + 1)) :
-- imply
  isingTorusAxisCorrelation (k := k) i beta n ^ 2 ≤ isingTorusAxisCorrelation (k := k) i beta (n - 1) * isingTorusAxisCorrelation (k := k) i beta (n + 1) := by
-- proof
  apply StatMech.FrontierA.isingTorusAxisCorrelation_logConvex i beta hbeta n hn2 hnH

/--
[isingTorusAxisCorrelation_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisMonotonicity.lean)
-/
@[path]
private lemma isingTorusAxisCorrelation_succ_le_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 ≤ beta)
  (hn : n < 2 ^ (k + 1)) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i (n + 1)) ≤ isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i n) := by
-- proof
  apply StatMech.FrontierA.isingTorusAxisCorrelation_succ_le i beta hbeta n hn


-- created on 2026-10-23
