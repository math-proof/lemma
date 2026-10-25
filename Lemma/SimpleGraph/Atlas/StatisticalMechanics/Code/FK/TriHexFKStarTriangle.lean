import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexFKStarTriangle
open Finset StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangleFKTerminalPartition_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma triangleFKTerminalPartition_eq_eq
  {y0 y1 y2 : Real} :
-- imply
  triangleFKTerminalPartition y0 y1 y2 = 1 + y0 + y1 + y2 + (y0 * y1 + y1 * y2 + y2 * y0 + y0 * y1 * y2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKTerminalPartition_eq y0 y1 y2

/--
[starFKTerminalPartition_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma starFKTerminalPartition_eq_eq
  {q y0 y1 y2 : Real} :
-- imply
  starFKTerminalPartition q y0 y1 y2 = q + y0 + y1 + y2 + y0 * y1 + y1 * y2 + y2 * y0 + y0 * y1 * y2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.starFKTerminalPartition_eq q y0 y1 y2

/--
[triangleFKTerminalPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma triangleFKTerminalPartition_pos_eq
  {y0 y1 y2 : Real}
-- given
  (hy0 : 0 < y0)
  (hy1 : 0 < y1)
  (hy2 : 0 < y2) :
-- imply
  0 < triangleFKTerminalPartition y0 y1 y2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKTerminalPartition_pos hy0 hy1 hy2

/--
[starFKTerminalPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma starFKTerminalPartition_pos_eq
  {q y0 y1 y2 : Real}
-- given
  (hq : 0 < q)
  (hy0 : 0 < y0)
  (hy1 : 0 < y1)
  (hy2 : 0 < y2) :
-- imply
  0 < starFKTerminalPartition q y0 y1 y2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.starFKTerminalPartition_pos hq hy0 hy1 hy2

/--
[triangleFKTerminalProbability_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma triangleFKTerminalProbability_sum_eq_one_eq
  {y0 y1 y2 : Real}
-- given
  (hy0 : 0 < y0)
  (hy1 : 0 < y1)
  (hy2 : 0 < y2) :
-- imply
  (∑ c, triangleFKTerminalProbability y0 y1 y2 c) = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKTerminalProbability_sum_eq_one hy0 hy1 hy2

/--
[starFKTerminalProbability_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma starFKTerminalProbability_sum_eq_one_eq
  {q y0 y1 y2 : Real}
-- given
  (hq : 0 < q)
  (hy0 : 0 < y0)
  (hy1 : 0 < y1)
  (hy2 : 0 < y2) :
-- imply
  (∑ c, starFKTerminalProbability q y0 y1 y2 c) = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.starFKTerminalProbability_sum_eq_one hq hy0 hy1 hy2

/--
[triHexFK_terminalWeight_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma triHexFK_terminalWeight_identity_eq
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
  {c : ThreeTerminalConnectivity}
-- given
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  (y0 * y1 * y2) * starFKTerminalWeight q y0Star y1Star y2Star c = q ^ 2 * triangleFKTerminalWeight y0 y1 y2 c := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_terminalWeight_identity h0 h1 h2 hsurface c

/--
[triHexFK_terminalPartition_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma triHexFK_terminalPartition_identity_eq
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
-- given
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  (y0 * y1 * y2) * starFKTerminalPartition q y0Star y1Star y2Star = q ^ 2 * triangleFKTerminalPartition y0 y1 y2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_terminalPartition_identity h0 h1 h2 hsurface

/--
[triHexFK_terminalProbability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma triHexFK_terminalProbability_eq_eq
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
  {c : ThreeTerminalConnectivity}
-- given
  (hq : 0 < q)
  (hy0 : 0 < y0)
  (hy1 : 0 < y1)
  (hy2 : 0 < y2)
  (hy0Star : 0 < y0Star)
  (hy1Star : 0 < y1Star)
  (hy2Star : 0 < y2Star)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  starFKTerminalProbability q y0Star y1Star y2Star c = triangleFKTerminalProbability y0 y1 y2 c := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_terminalProbability_eq hq hy0 hy1 hy2 hy0Star hy1Star hy2Star h0 h1 h2 hsurface c

/--
[triHexFK_terminalLaw_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma triHexFK_terminalLaw_eq_eq
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
-- given
  (hq : 0 < q)
  (hy0 : 0 < y0)
  (hy1 : 0 < y1)
  (hy2 : 0 < y2)
  (hy0Star : 0 < y0Star)
  (hy1Star : 0 < y1Star)
  (hy2Star : 0 < y2Star)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  starFKTerminalProbability q y0Star y1Star y2Star = triangleFKTerminalProbability y0 y1 y2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_terminalLaw_eq hq hy0 hy1 hy2 hy0Star hy1Star hy2Star h0 h1 h2 hsurface

/--
[triHexFK_terminalLaw_dualParam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean)
-/
@[path]
private lemma triHexFK_terminalLaw_dualParam_eq
  {q p0 p1 p2 : Real}
-- given
  (hq : 0 < q)
  (hp0 : p0 ∈ Set.Ioo (0 : Real) 1)
  (hp1 : p1 ∈ Set.Ioo (0 : Real) 1)
  (hp2 : p2 ∈ Set.Ioo (0 : Real) 1)
  (hsurface : triangularFKCriticalSurface q (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) = 0) :
-- imply
  starFKTerminalProbability q (fkEdgeOdds (BeffaraDC.dualParam p0 q)) (fkEdgeOdds (BeffaraDC.dualParam p1 q)) (fkEdgeOdds (BeffaraDC.dualParam p2 q)) = triangleFKTerminalProbability (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_terminalLaw_dualParam hq hp0 hp1 hp2 hsurface


-- created on 2026-10-23
