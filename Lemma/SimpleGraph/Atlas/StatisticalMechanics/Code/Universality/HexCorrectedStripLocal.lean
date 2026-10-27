import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLocal.Part3
open StatMech StatMech.Universality


/--
[hexCS_anchored_partner_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_anchored_partner_valid_eq
  {a : ℂ}
  {base tail : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hvalid : (ofTurns a h0 (base ++ ((1 : ℤ) :: tail))).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ ((1 : ℤ) :: tail))).StaysIn region)
  (hsum : ((1 : ℤ) :: tail).sum = -4)
  (hclose : let m := hexInfra_midAccum a h0 base let h := hexInfra_headAccum h0 base hexInfra_midAccum m h ((1 : ℤ) :: tail) + halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) = m + halfStep h) :
-- imply
  (ofTurns a h0 (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).StaysIn region ∧ (ofTurns a h0 (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).EndsAt (hexInfra_midAccum a h0 base + halfStep (hexInfra_headAccum h0 base) + halfStep (hexInfra_headAccum h0 base + 1)) := by
-- proof
  apply StatMech.Universality.hexCS_anchored_partner_valid region a h0 base tail hvalid hsum hclose

/--
[hexCS_midAccum_add_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_midAccum_add_six_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_midAccum m (h + 6) ts = hexInfra_midAccum m h ts := by
-- proof
  apply StatMech.Universality.hexCS_midAccum_add_six m h ts

/--
[hexCS_midsAux_add_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_midsAux_add_six_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  midsAux m (h + 6) ts = midsAux m h ts := by
-- proof
  apply StatMech.Universality.hexCS_midsAux_add_six m h ts

/--
[hexCS_verticesAux_add_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_verticesAux_add_six_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  verticesAux m (h + 6) ts = verticesAux m h ts := by
-- proof
  apply StatMech.Universality.hexCS_verticesAux_add_six m h ts

/--
[hexCS_anchoredLoopReverse_midsAux_eq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_anchoredLoopReverse_midsAux_eq_neg_eq
  {m : ℂ}
  {tail : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ (-1 : ℤ) :: tail, t = 1 ∨ t = -1)
  (hsum : ((-1 : ℤ) :: tail).sum = 4)
  (hclose : hexInfra_midAccum m h ((-1 : ℤ) :: tail) + halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) = m + halfStep h) :
-- imply
  midsAux m h (anchoredLoopReverse ((-1 : ℤ) :: tail)) = m :: (midsAux m h ((-1 : ℤ) :: tail)).tail.reverse := by
-- proof
  apply StatMech.Universality.hexCS_anchoredLoopReverse_midsAux_eq_neg m h tail hlegal hsum hclose

/--
[hexCS_anchoredLoopReverse_midAccum_eq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_anchoredLoopReverse_midAccum_eq_neg_eq
  {m : ℂ}
  {tail : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ (-1 : ℤ) :: tail, t = 1 ∨ t = -1)
  (hsum : ((-1 : ℤ) :: tail).sum = 4)
  (hclose : hexInfra_midAccum m h ((-1 : ℤ) :: tail) + halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) = m + halfStep h) :
-- imply
  hexInfra_midAccum m h (anchoredLoopReverse ((-1 : ℤ) :: tail)) = m + halfStep h + halfStep (h - 1) := by
-- proof
  apply StatMech.Universality.hexCS_anchoredLoopReverse_midAccum_eq_neg m h tail hlegal hsum hclose

/--
[hexCS_anchoredLoopReverse_verticesAux_eq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_anchoredLoopReverse_verticesAux_eq_neg_eq
  {m : ℂ}
  {tail : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ (-1 : ℤ) :: tail, t = 1 ∨ t = -1)
  (hsum : ((-1 : ℤ) :: tail).sum = 4)
  (hclose : hexInfra_midAccum m h ((-1 : ℤ) :: tail) + halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) = m + halfStep h) :
-- imply
  verticesAux m h (anchoredLoopReverse ((-1 : ℤ) :: tail)) = (m + halfStep h) :: (verticesAux m h ((-1 : ℤ) :: tail)).dropLast.tail.reverse ++ [m + halfStep h] := by
-- proof
  apply StatMech.Universality.hexCS_anchoredLoopReverse_verticesAux_eq_neg m h tail hlegal hsum hclose

/--
[hexCS_anchoredLoopReverse_endpointVertices_eq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_anchoredLoopReverse_endpointVertices_eq_neg_eq
  {m : ℂ}
  {tail : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ (-1 : ℤ) :: tail, t = 1 ∨ t = -1)
  (hsum : ((-1 : ℤ) :: tail).sum = 4)
  (hclose : hexInfra_midAccum m h ((-1 : ℤ) :: tail) + halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) = m + halfStep h) :
-- imply
  (verticesAux m h (anchoredLoopReverse ((-1 : ℤ) :: tail))).dropLast = (m + halfStep h) :: (verticesAux m h ((-1 : ℤ) :: tail)).dropLast.tail.reverse := by
-- proof
  apply StatMech.Universality.hexCS_anchoredLoopReverse_endpointVertices_eq_neg m h tail hlegal hsum hclose

/--
[hexCS_anchored_partner_valid_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_anchored_partner_valid_neg_eq
  {a : ℂ}
  {base tail : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hvalid : (ofTurns a h0 (base ++ ((-1 : ℤ) :: tail))).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ ((-1 : ℤ) :: tail))).StaysIn region)
  (hsum : ((-1 : ℤ) :: tail).sum = 4)
  (hclose : let m := hexInfra_midAccum a h0 base let h := hexInfra_headAccum h0 base hexInfra_midAccum m h ((-1 : ℤ) :: tail) + halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) = m + halfStep h) :
-- imply
  (ofTurns a h0 (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).StaysIn region ∧ (ofTurns a h0 (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).EndsAt (hexInfra_midAccum a h0 base + halfStep (hexInfra_headAccum h0 base) + halfStep (hexInfra_headAccum h0 base - 1)) := by
-- proof
  apply StatMech.Universality.hexCS_anchored_partner_valid_neg region a h0 base tail hvalid hsum hclose

/--
[HexEndpointLocalCrossing.after_eq_cyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma after_eq_cyclic_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
-- imply
  (ts[C.index]'C.index_lt = 1 → C.after = hexCyclicPred C.before) ∧ (ts[C.index]'C.index_lt = -1 → C.after = hexCyclicSucc C.before) := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.after_eq_cyclic C hlegal

/--
[HexEndpointLocalCrossing.endEdge_eq_cyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma endEdge_eq_cyclic_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  (ts[C.index]'C.index_lt = 1 → endEdge = hexCyclicSucc C.before) ∧ (ts[C.index]'C.index_lt = -1 → endEdge = hexCyclicPred C.before) := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.endEdge_eq_cyclic C hnotOutside hlegal endEdge hend hcount

/--
[hexCS_cyclicLoopPair_of_selected_terminal_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_cyclicLoopPair_of_selected_terminal_cycle_eq
  {T L : ℕ}
  {hT : 0 < T}
  {c : HexAWCoord}
  {endEdge : Fin 3}
  {ts : List ℤ}
  {C : HexEndpointLocalCrossing ts c}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3)
  (horient : (ts[C.index]'C.index_lt = 1 ∧ (ts.drop C.index).sum = -4) ∨ (ts[C.index]'C.index_lt = -1 ∧ (ts.drop C.index).sum = 4)) :
-- imply
  ∃ P : HexEndpointCyclicLoopPair (hexCSFiniteRegion T L hT).inRegion hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c), ts ∈ P.piece ∧ hexInfra_midAccum hexAWStart 1 P.base + halfStep (hexInfra_headAccum 1 P.base) = hexAWPos c ∧ ∀ u ∈ P.piece, specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) u = 3 := by
-- proof
  apply StatMech.Universality.hexCS_cyclicLoopPair_of_selected_terminal_cycle c endEdge ts C hnotOutside hadm hcount horient

/--
[HexEndpointLocalCrossing.after_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma after_heading_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
-- imply
  let base := ts.take C.index let t := ts[C.index]'C.index_lt let h := hexInfra_headAccum 1 base hexCSHeadingFin (h + t) = hexAWHeadingMod c C.after := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.after_heading C hlegal

/--
[HexEndpointLocalCrossing.edgeOf_after_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma edgeOf_after_heading_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
-- imply
  let base := ts.take C.index let t := ts[C.index]'C.index_lt let h := hexInfra_headAccum 1 base HexCSHeadingFits c (hexCSHeadingFin (h + t)) ∧ hexCSEdgeOfHeading c (hexCSHeadingFin (h + t)) = C.after := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.edgeOf_after_heading C hlegal

/--
[HexEndpointLocalCrossing.terminalCoordPath_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma terminalCoordPath_pos_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
-- imply
  let base := ts.take C.index let t := ts[C.index]'C.index_lt let tail := ts.drop (C.index + 1) let m := hexInfra_midAccum hexAWStart 1 base let h := hexInfra_headAccum 1 base (hexCSCoordPath c (hexCSHeadingFin (h + t)) tail).map hexAWPos = verticesAux m h (t :: tail) := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.terminalCoordPath_pos C hlegal

/--
[HexEndpointLocalCrossing.final_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma final_heading_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  hexCSHeadingFin (hexInfra_headAccum 1 ts) = hexCSHeadingFin (hexAWHeading c endEdge + 3) := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.final_heading C hnotOutside hlegal endEdge hend hcount

/--
[HexEndpointLocalCrossing.closing_brick_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma closing_brick_identity_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  let base := ts.take C.index let t := ts[C.index]'C.index_lt let tail := ts.drop (C.index + 1) let h := hexInfra_headAccum 1 base let H := hexInfra_headAccum (h + t) tail 2 * (-t) + 3 * ons_turnPow (hexBrickDir (hexCSHeadingFin H)) (hexBrickDir (hexCSHeadingFin (h + t))) = hexBrickTurnPotential (hexCSHeadingFin (h + t)) - hexBrickTurnPotential (hexCSHeadingFin H) := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.closing_brick_identity C hnotOutside hlegal endEdge hend hcount

/--
[HexEndpointLocalCrossing.terminalBrick_closed_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma terminalBrick_closed_nodup_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  let base := ts.take C.index let t := ts[C.index]'C.index_lt let tail := ts.drop (C.index + 1) let h := hexInfra_headAccum 1 base let dirs := hexCSBrickDirections (h + t) tail ons_pathDisplacement dirs = 0 ∧ (ons_pathVertices dirs).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.terminalBrick_closed_nodup C hnotOutside hlegal endEdge hend hcount

/--
[HexEndpointLocalCrossing.terminalBlock_length_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma terminalBlock_length_ge_three_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  3 ≤ (ts.drop C.index).length := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.terminalBlock_length_ge_three C hnotOutside hlegal endEdge hend hcount

/--
[HexEndpointLocalCrossing.terminalBlock_sum_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma terminalBlock_sum_cases_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3)
  (hlen : 3 ≤ (ts.drop C.index).length) :
-- imply
  (ts[C.index]'C.index_lt = 1 ∧ ((ts.drop C.index).sum = -4 ∨ (ts.drop C.index).sum = 8)) ∨ (ts[C.index]'C.index_lt = -1 ∧ ((ts.drop C.index).sum = 4 ∨ (ts.drop C.index).sum = -8)) := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.terminalBlock_sum_cases C hnotOutside hlegal endEdge hend hcount hlen

/--
[HexEndpointLocalCrossing.terminalBlock_sum_cases_auto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma terminalBlock_sum_cases_auto_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  (ts[C.index]'C.index_lt = 1 ∧ ((ts.drop C.index).sum = -4 ∨ (ts.drop C.index).sum = 8)) ∨ (ts[C.index]'C.index_lt = -1 ∧ ((ts.drop C.index).sum = 4 ∨ (ts.drop C.index).sum = -8)) := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.terminalBlock_sum_cases_auto C hnotOutside hlegal endEdge hend hcount

/--
[HexEndpointLocalCrossing.terminal_selected_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma terminal_selected_side_eq
  {T L : ℕ}
  {hT : 0 < T}
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  let base := ts.take C.index let t := ts[C.index]'C.index_lt let tail := ts.drop (C.index + 1) let h := hexInfra_headAccum 1 base HexCSTerminalSelectedSide t h tail := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.terminal_selected_side C hnotOutside endEdge hadm hcount

/--
[HexEndpointLocalCrossing.selected_terminal_cycle_of_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma selected_terminal_cycle_of_side_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3)
  (hside : let base := ts.take C.index let t := ts[C.index]'C.index_lt let tail := ts.drop (C.index + 1) let h := hexInfra_headAccum 1 base HexCSTerminalSelectedSide t h tail) :
-- imply
  (ts[C.index]'C.index_lt = 1 ∧ (ts.drop C.index).sum = -4) ∨ (ts[C.index]'C.index_lt = -1 ∧ (ts.drop C.index).sum = 4) := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.selected_terminal_cycle_of_side C hnotOutside hlegal endEdge hend hcount hside

/--
[hexCS_cyclicLoopPair_of_terminal_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_cyclicLoopPair_of_terminal_side_eq
  {T L : ℕ}
  {hT : 0 < T}
  {c : HexAWCoord}
  {endEdge : Fin 3}
  {ts : List ℤ}
  {C : HexEndpointLocalCrossing ts c}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3)
  (hside : let base := ts.take C.index let t := ts[C.index]'C.index_lt let tail := ts.drop (C.index + 1) let h := hexInfra_headAccum 1 base HexCSTerminalSelectedSide t h tail) :
-- imply
  ∃ P : HexEndpointCyclicLoopPair (hexCSFiniteRegion T L hT).inRegion hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c), ts ∈ P.piece := by
-- proof
  apply StatMech.Universality.hexCS_cyclicLoopPair_of_terminal_side c endEdge ts C hnotOutside hadm hcount hside

/--
[hexCS_cyclicLoopPair_of_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_cyclicLoopPair_of_terminal_eq
  {T L : ℕ}
  {hT : 0 < T}
  {c : HexAWCoord}
  {endEdge : Fin 3}
  {ts : List ℤ}
  {C : HexEndpointLocalCrossing ts c}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  ∃ P : HexEndpointCyclicLoopPair (hexCSFiniteRegion T L hT).inRegion hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c), ts ∈ P.piece := by
-- proof
  apply StatMech.Universality.hexCS_cyclicLoopPair_of_terminal c endEdge ts C hnotOutside hadm hcount

/--
[hexCS_localRelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean)
-/
@[path]
private lemma hexCS_localRelation_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  HexCSLocalRelation T L hT := by
-- proof
  apply StatMech.Universality.hexCS_localRelation T L hT


-- created on 2026-10-23
