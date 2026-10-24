import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc_core
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc_adj_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_adj_cases_eq
  {v w : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj v w) :
-- imply
  v = w + ![1, 0] ∨ v = w + ![-1, 0] ∨ v = w + ![0, 1] ∨ v = w + ![0, -1] := by
-- proof
  apply StatMech.Walls.jc_adj_cases v w hadj

/--
[jc_shift_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_shift_add_eq
  {c : Site 2}
  {i j : ℤ} :
-- imply
  (c + ![i, 0] : Site 2) + ![j, 0] = c + ![i + j, 0] := by
-- proof
  apply StatMech.Walls.jc_shift_add c i j

/--
[jc_rightEnd_pendant_of_down_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_rightEnd_pendant_of_down_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len)
  (hlen : 1 ≤ len)
  (hdown : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
-- imply
  jc_IsPendantCell K (c + ![len, 0]) := by
-- proof
  apply StatMech.Walls.jc_rightEnd_pendant_of_down_nmem K c len hrun hlen hdown

/--
[jc_cellConnected_diff_rightEnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_cellConnected_diff_rightEnd_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hconn : CellConnected K)
  (hrun : jc_IsTopRowRun K c len)
  (hlen : 1 ≤ len)
  (hdown : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
-- imply
  CellConnected (K \ {(c + ![len, 0] : Site 2)}) := by
-- proof
  apply StatMech.Walls.jc_cellConnected_diff_rightEnd K c len hconn hrun hlen hdown

/--
[jc_balancePreservingContraction_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_balancePreservingContraction_of_saturating_eq
-- given
  (h : jc_BalanceSaturatingContraction) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Walls.jc_balancePreservingContraction_of_saturating h

/--
[jc_core_iff_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_core_iff_saturating_eq :
-- imply
  BalancePreservingContraction ↔ jc_BalanceSaturatingContraction := by
-- proof
  apply StatMech.Walls.jc_core_iff_saturating

/--
[jc_turningIsFullRevolution_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_turningIsFullRevolution_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : jc_BalanceSaturatingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Walls.jc_turningIsFullRevolution_of_saturating h K hK hne a

/--
[jc_starHull_turningIsFullRevolution_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_starHull_turningIsFullRevolution_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : jc_BalanceSaturatingContraction)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  TurningIsFullRevolution (ndt_StarHull K) a := by
-- proof
  apply StatMech.Walls.jc_starHull_turningIsFullRevolution_of_saturating h K hSK hne a

/--
[jc_starHull_totalTurn_eq_four_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_starHull_totalTurn_eq_four_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : jc_BalanceSaturatingContraction)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Walls.jc_starHull_totalTurn_eq_four_of_saturating h K hSK hne a

/--
[jc_unitCell_core_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_unitCell_core_balanceIsFour_eq :
-- imply
  BalanceIsFour unitCell ucBase := by
-- proof
  apply StatMech.Walls.jc_unitCell_core_balanceIsFour

/--
[jc_domino_core_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_domino_core_witness_eq :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase := by
-- proof
  apply StatMech.Walls.jc_domino_core_witness

/--
[jc_domino_rightEnd_pendant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_core.lean)
-/
@[path]
private lemma jc_domino_rightEnd_pendant_eq :
-- imply
  jc_IsPendantCell domino ((![0, 0] : Site 2) + ![1, 0]) := by
-- proof
  apply StatMech.Walls.jc_domino_rightEnd_pendant


-- created on 2026-10-23
