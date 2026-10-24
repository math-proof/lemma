import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc3_core
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc3_pendantClipMatch_of_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_pendantClipMatch_of_splice_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (h : jc3_OrbitSpliceDatum K a r) :
-- imply
  jc2_PendantClipMatch K a r := by
-- proof
  apply StatMech.Walls.jc3_pendantClipMatch_of_splice K a r h

/--
[jc3_saturatingEarMatch_of_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_saturatingEarMatch_of_splice_eq
-- given
  (h : jc3_SaturatingOrbitSplice) :
-- imply
  jc2_SaturatingEarMatch := by
-- proof
  apply StatMech.Walls.jc3_saturatingEarMatch_of_splice h

/--
[jc3_splice_thin_or_thick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_splice_thin_or_thick_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hframe : jc2_RunFrame K c len)
  (hlen : 1 ≤ len) :
-- imply
  (jc2_rightEnd c len + ![0, -1] ∉ K ∧ jc_IsPendantCell K (jc2_rightEnd c len)) ∨ (jc2_rightEnd c len + ![0, -1] ∈ K ∧ ¬ jc_IsPendantCell K (jc2_rightEnd c len)) := by
-- proof
  apply StatMech.Walls.jc3_splice_thin_or_thick K c len hframe hlen

/--
[jc3_thin_reroute_cellConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_thin_reroute_cellConnected_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hconn : CellConnected K)
  (hframe : jc2_RunFrame K c len)
  (hlen : 1 ≤ len)
  (hthin : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
-- imply
  CellConnected (K \ {(c + ![len, 0] : Site 2)}) := by
-- proof
  apply StatMech.Walls.jc3_thin_reroute_cellConnected K c len hconn hframe hlen hthin

/--
[jc3_thick_reroute_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_thick_reroute_target_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hthick : jc2_FullyThick K c len)
  (hlen : 0 ≤ len) :
-- imply
  jc3_downCell c len ∈ K \ {jc3_runRightEnd c len} ∧ (hypercubicLattice 2).Adj (jc3_runRightEnd c len) (jc3_downCell c len) := by
-- proof
  apply StatMech.Walls.jc3_thick_reroute_target K c len hthick hlen

/--
[jc3_balanceSaturatingContraction_of_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_balanceSaturatingContraction_of_splice_eq
-- given
  (h : jc3_SaturatingOrbitSplice) :
-- imply
  bpc_BalanceSaturatingContraction := by
-- proof
  apply StatMech.Walls.jc3_balanceSaturatingContraction_of_splice h

/--
[jc3_balancePreservingContraction_of_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_balancePreservingContraction_of_splice_eq
-- given
  (h : jc3_SaturatingOrbitSplice) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Walls.jc3_balancePreservingContraction_of_splice h

/--
[jc3_starHull_totalTurn_eq_four_of_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_starHull_totalTurn_eq_four_of_splice_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : jc3_SaturatingOrbitSplice)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Walls.jc3_starHull_totalTurn_eq_four_of_splice h K hSK hne a

/--
[jc3_pendantClipMatch_of_splice'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_pendantClipMatch_of_splice'_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2} :
-- imply
  jc3_OrbitSpliceDatum K a r → jc2_PendantClipMatch K a r := by
-- proof
  apply StatMech.Walls.jc3_pendantClipMatch_of_splice' K a r

/--
[jc3_domino_core_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_domino_core_witness_eq :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase := by
-- proof
  apply StatMech.Walls.jc3_domino_core_witness

/--
[jc3_domino_thin_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_domino_thin_ear_eq :
-- imply
  jc_IsPendantCell domino ((![0, 0] : Site 2) + ![1, 0]) := by
-- proof
  apply StatMech.Walls.jc3_domino_thin_ear

/--
[jc3_domino_thin_clip_cellConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean)
-/
@[path]
private lemma jc3_domino_thin_clip_cellConnected_eq :
-- imply
  CellConnected (domino \ {(![0, 0] : Site 2) + ![1, 0]}) := by
-- proof
  apply StatMech.Walls.jc3_domino_thin_clip_cellConnected


-- created on 2026-10-23
