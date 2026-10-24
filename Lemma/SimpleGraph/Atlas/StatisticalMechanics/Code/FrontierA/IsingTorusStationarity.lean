import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingTorusStationarity
open Finset StatMech StatMech.FrontierA


/--
[isingTorusTwoPoint_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusStationarity.lean)
-/
@[path]
private lemma isingTorusTwoPoint_translate_eq
  {d k : Nat}
  {a x y : IsingDyadicTorus d k}
  {beta : Real} :
-- imply
  isingTorusTwoPoint beta (x + a) (y + a) = isingTorusTwoPoint beta x y := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_translate a x y beta

/--
[isingTorusTwoPoint_eq_origin_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusStationarity.lean)
-/
@[path]
private lemma isingTorusTwoPoint_eq_origin_displacement_eq
  {d k : Nat}
  {x y : IsingDyadicTorus d k}
  {beta : Real} :
-- imply
  isingTorusTwoPoint beta x y = isingTorusTwoPoint beta 0 (y - x) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_eq_origin_displacement x y beta

/--
[isingTorusAveragedTwoPoint_eq_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusStationarity.lean)
-/
@[path]
private lemma isingTorusAveragedTwoPoint_eq_twoPoint_eq
  {d k : Nat}
  {beta : Real}
  {z : IsingDyadicTorus d k} :
-- imply
  isingTorusAveragedTwoPoint beta z = isingTorusTwoPoint beta 0 z := by
-- proof
  apply StatMech.FrontierA.isingTorusAveragedTwoPoint_eq_twoPoint beta z

/--
[isingTorusTwoPoint_difference_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusStationarity.lean)
-/
@[path]
private lemma isingTorusTwoPoint_difference_abs_le_eq
  {d k : Nat}
  {beta : Real}
  {x y : IsingDyadicTorus d k}
-- given
  (hbeta : 0 < beta) :
-- imply
  |isingTorusTwoPoint beta 0 x - isingTorusTwoPoint beta 0 y| ≤ (1 / Fintype.card (IsingDyadicTorus d k) : Real) * ∑ chi ∈ (Finset.univ.erase (0 : AddChar (IsingDyadicTorus d k) Complex)), ((1 / beta) / isingTorusCharacterDispersion chi) * ‖starRingEnd Complex (chi x) - starRingEnd Complex (chi y)‖ := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_difference_abs_le beta hbeta x y


-- created on 2026-10-23
