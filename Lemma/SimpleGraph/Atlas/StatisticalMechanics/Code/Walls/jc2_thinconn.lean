import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinconn
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc2_thinFingerClip_cellConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinconn.lean)
-/
@[path]
private lemma jc2_thinFingerClip_cellConnected_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hconn : CellConnected K)
  (hrun : jc_IsTopRowRun K c len)
  (hlen : 1 ≤ len)
  (hthin : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
-- imply
  CellConnected (K \ {(c + ![len, 0] : Site 2)}) := by
-- proof
  apply StatMech.Walls.jc2_thinFingerClip_cellConnected K c len hconn hrun hlen hthin

/--
[jc2_thinFingerClip_cellConnected'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinconn.lean)
-/
@[path]
private lemma jc2_thinFingerClip_cellConnected'_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
  {r : Site 2}
-- given
  (hr : r = c + ![len, 0])
  (hconn : CellConnected K)
  (hrun : jc_IsTopRowRun K c len)
  (hlen : 1 ≤ len)
  (hthin : (r + ![0, -1] : Site 2) ∉ K) :
-- imply
  CellConnected (K \ {r}) := by
-- proof
  apply StatMech.Walls.jc2_thinFingerClip_cellConnected' K c len r hr hconn hrun hlen hthin

/--
[jc2_thinConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinconn.lean)
-/
@[path]
private lemma jc2_thinConn_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hconn : CellConnected K)
  (hrun : jc_IsTopRowRun K c len)
  (hlen : 1 ≤ len)
  (hthin : (c + ![len, -1] : Site 2) ∉ K) :
-- imply
  CellConnected (K \ {(c + ![len, 0] : Site 2)}) := by
-- proof
  apply StatMech.Walls.jc2_thinConn K c len hconn hrun hlen hthin

/--
[jc2_jc_domino_eq_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinconn.lean)
-/
@[path]
private lemma jc2_jc_domino_eq_domino_eq :
-- imply
  jc_domino = domino := by
-- proof
  apply StatMech.Walls.jc2_jc_domino_eq_domino

/--
[jc2_domino_cellConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinconn.lean)
-/
@[path]
private lemma jc2_domino_cellConnected_eq :
-- imply
  CellConnected domino := by
-- proof
  apply StatMech.Walls.jc2_domino_cellConnected

/--
[jc2_domino_thinConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinconn.lean)
-/
@[path]
private lemma jc2_domino_thinConn_eq :
-- imply
  CellConnected (domino \ {(![0, 0] : Site 2) + ![1, 0]}) := by
-- proof
  apply StatMech.Walls.jc2_domino_thinConn


-- created on 2026-10-23
