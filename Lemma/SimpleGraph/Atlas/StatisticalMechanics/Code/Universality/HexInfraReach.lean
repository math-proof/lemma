import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexInfraReach
open StatMech StatMech.Universality


/--
[hexInfra_lastVertex_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_lastVertex_re_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)).re = a.re + hexInfra_disp h0 ts := by
-- proof
  apply StatMech.Universality.hexInfra_lastVertex_re a h0 ts

/--
[hexInfra_reachesWidth_of_dispBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_reachesWidth_of_dispBridge_eq
  {a : ℂ}
  {b : HexBridge}
-- given
  (h0 : ℤ)
  (hb : hexInfra_IsDispBridge h0 b) :
-- imply
  hexWall3_ReachesWidth a h0 b.width b.content := by
-- proof
  apply StatMech.Universality.hexInfra_reachesWidth_of_dispBridge a h0 b hb

/--
[hexInfra_dispBridge_colDomination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_dispBridge_colDomination_eq
  {a : ℂ}
  {b : HexBridge}
  {χ : ℝ}
  (hsummable hle_one)
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx0 : 0 ≤ x)
  (hχ : 0 < χ)
  (hxχ : x ≤ χ)
  (hb : hexInfra_IsDispBridge h0 b)
  (hSAW : (HexWalk.ofTurns a h0 b.content).IsLegalSAW) :
-- imply
  x ^ (HexWalk.ofTurns a h0 b.content).numVertices ≤ (hexWall3_column a h0 b.width χ hsummable hle_one).colSum x := by
-- proof
  apply StatMech.Universality.hexInfra_dispBridge_colDomination a h0 b χ hx0 hχ hxχ hb hSAW

/--
[hexInfra_dispBridgeOfContent_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_dispBridgeOfContent_content_eq
  {ts : List ℤ}
  (hne hpos)
-- given
  (h0 : ℤ) :
-- imply
  (hexInfra_dispBridgeOfContent h0 ts hne hpos).content = ts := by
-- proof
  apply StatMech.Universality.hexInfra_dispBridgeOfContent_content h0 ts

/--
[hexInfra_dispBridgeOfContent_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_dispBridgeOfContent_width_eq
  {ts : List ℤ}
  (hne hpos)
-- given
  (h0 : ℤ) :
-- imply
  (hexInfra_dispBridgeOfContent h0 ts hne hpos).width = ⌊hexInfra_disp h0 ts⌋₊ := by
-- proof
  apply StatMech.Universality.hexInfra_dispBridgeOfContent_width h0 ts

/--
[hexInfra_dispBridgeOfContent_isDispBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_dispBridgeOfContent_isDispBridge_eq
  {ts : List ℤ}
  (hne hpos)
-- given
  (h0 : ℤ)
  (hd : 0 ≤ hexInfra_disp h0 ts) :
-- imply
  hexInfra_IsDispBridge h0 (hexInfra_dispBridgeOfContent h0 ts hne hpos) := by
-- proof
  apply StatMech.Universality.hexInfra_dispBridgeOfContent_isDispBridge h0 ts hd

/--
[hexInfra_dispBridgeOfContent_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_dispBridgeOfContent_reaches_eq
  {a : ℂ}
  {ts : List ℤ}
  (hne hpos)
-- given
  (h0 : ℤ)
  (hd : 0 ≤ hexInfra_disp h0 ts) :
-- imply
  hexWall3_ReachesWidth a h0 (hexInfra_dispBridgeOfContent h0 ts hne hpos).width (hexInfra_dispBridgeOfContent h0 ts hne hpos).content := by
-- proof
  apply StatMech.Universality.hexInfra_dispBridgeOfContent_reaches a h0 ts hd

/--
[hexInfra_disp_singleRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_disp_singleRight_eq :
-- imply
  hexInfra_disp 0 [(-1 : ℤ)] = (HexWalk.halfStep 0).re + 2 * (HexWalk.halfStep (-1)).re := by
-- proof
  apply StatMech.Universality.hexInfra_disp_singleRight

/--
[hexInfra_disp_singleRight_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_disp_singleRight_ge_one_eq :
-- imply
  (1 : ℝ) ≤ hexInfra_disp 0 [(-1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hexInfra_disp_singleRight_ge_one

/--
[hexInfra_disp_singleRight_lt_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_disp_singleRight_lt_two_eq :
-- imply
  hexInfra_disp 0 [(-1 : ℤ)] < 2 := by
-- proof
  apply StatMech.Universality.hexInfra_disp_singleRight_lt_two

/--
[hexInfra_floor_disp_singleRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_floor_disp_singleRight_eq :
-- imply
  ⌊hexInfra_disp 0 [(-1 : ℤ)]⌋₊ = 1 := by
-- proof
  apply StatMech.Universality.hexInfra_floor_disp_singleRight

/--
[hexInfra_witnessDispBridge_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_witnessDispBridge_width_eq :
-- imply
  hexInfra_witnessDispBridge.width = 1 := by
-- proof
  apply StatMech.Universality.hexInfra_witnessDispBridge_width

/--
[hexInfra_witnessDispBridge_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_witnessDispBridge_content_eq :
-- imply
  hexInfra_witnessDispBridge.content = [(-1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hexInfra_witnessDispBridge_content

/--
[hexInfra_singleRight_isDispBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_singleRight_isDispBridge_eq :
-- imply
  hexInfra_IsDispBridge 0 hexInfra_witnessDispBridge := by
-- proof
  apply StatMech.Universality.hexInfra_singleRight_isDispBridge

/--
[hexInfra_witnessDispBridge_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean)
-/
@[path]
private lemma hexInfra_witnessDispBridge_reaches_eq
  {a : ℂ} :
-- imply
  hexWall3_ReachesWidth a 0 hexInfra_witnessDispBridge.width hexInfra_witnessDispBridge.content := by
-- proof
  apply StatMech.Universality.hexInfra_witnessDispBridge_reaches a


-- created on 2026-10-23
