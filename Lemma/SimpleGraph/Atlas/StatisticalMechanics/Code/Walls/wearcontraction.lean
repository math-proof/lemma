import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wearcontraction
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[wear_balancePreservingContraction_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wearcontraction.lean)
-/
@[path]
private lemma wear_balancePreservingContraction_of_merge_eq
-- given
  (h : jc4_SaturatingMerge) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Walls.wear_balancePreservingContraction_of_merge h

/--
[wear_cornerBalance_eq_four_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wearcontraction.lean)
-/
@[path]
private lemma wear_cornerBalance_eq_four_of_merge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : jc4_SaturatingMerge)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  cornerBalance K a = 4 ∨ cornerBalance K a = -4 := by
-- proof
  apply StatMech.Walls.wear_cornerBalance_eq_four_of_merge h K hK hne a

/--
[wear_revCount_pm_one_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wearcontraction.lean)
-/
@[path]
private lemma wear_revCount_pm_one_of_merge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : jc4_SaturatingMerge)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Walls.wear_revCount_pm_one_of_merge h K hK hne a

/--
[wear_starHull_totalTurn_eq_four_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wearcontraction.lean)
-/
@[path]
private lemma wear_starHull_totalTurn_eq_four_of_merge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : jc4_SaturatingMerge)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Walls.wear_starHull_totalTurn_eq_four_of_merge h K hSK hne a

/--
[wear_extremeCell_convex_up_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wearcontraction.lean)
-/
@[path]
private lemma wear_extremeCell_convex_up_left_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  c + ![0, 1] ∉ K ∧ c + ![-1, 0] ∉ K := by
-- proof
  apply StatMech.Walls.wear_extremeCell_convex_up_left K c hc

/--
[wear_extremeCell_neighbor_right_or_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wearcontraction.lean)
-/
@[path]
private lemma wear_extremeCell_neighbor_right_or_down_eq
  {K : Set (Site 2)}
  {c v : Site 2}
-- given
  (hc : IsExtremeCell K c)
  (hv : v ∈ K)
  (hadj : (hypercubicLattice 2).Adj v c) :
-- imply
  v = c + ![1, 0] ∨ v = c + ![0, -1] := by
-- proof
  apply StatMech.Walls.wear_extremeCell_neighbor_right_or_down K c v hc hv hadj

/--
[wear_pendant_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wearcontraction.lean)
-/
@[path]
private lemma wear_pendant_contraction_eq
  {K : Set (Site 2)}
  {c : Site 2}
  [Fintype ↑(((hypercubicLattice 2).induce K).neighborSet (⟨c, hc⟩ : K))]
-- given
  (hc : c ∈ K)
  (hconn : CellConnected K)
  (hdeg : ((hypercubicLattice 2).induce K).degree (⟨c, hc⟩ : K) = 1) :
-- imply
  CellConnected (K \ {c}) := by
-- proof
  apply StatMech.Walls.wear_pendant_contraction K c hc hconn hdeg

/--
[wear_unitCell_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wearcontraction.lean)
-/
@[path]
private lemma wear_unitCell_cornerBalance_eq :
-- imply
  cornerBalance unitCell ucBase = 4 ∨ cornerBalance unitCell ucBase = -4 := by
-- proof
  apply StatMech.Walls.wear_unitCell_cornerBalance

/--
[wear_domino_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wearcontraction.lean)
-/
@[path]
private lemma wear_domino_cornerBalance_eq :
-- imply
  cornerBalance domino dmBase = 4 ∨ cornerBalance domino dmBase = -4 := by
-- proof
  apply StatMech.Walls.wear_domino_cornerBalance

/--
[wear_extremeCell_can_be_cutVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wearcontraction.lean)
-/
@[path]
private lemma wear_extremeCell_can_be_cutVertex_eq :
-- imply
  IsExtremeCell cutWitness ![1, 1] ∧ CellConnected cutWitness ∧ ¬ CellConnected (cutWitness \ {![1, 1]}) := by
-- proof
  apply StatMech.Walls.wear_extremeCell_can_be_cutVertex


-- created on 2026-10-23
