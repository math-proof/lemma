import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexStripBandClose
open StatMech StatMech.Universality StatMech.Universality.HexStripSimplyConnected


/--
[hexJordan_runningHead_eq_headAccum_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_runningHead_eq_headAccum_take_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hexStripWinding_runningHead h0 ts k = hexInfra_headAccum h0 (ts.take k) := by
-- proof
  apply StatMech.Universality.hexJordan_runningHead_eq_headAccum_take h0 ts k

/--
[hexJordan_midsAux_getElem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_midsAux_getElem_eq
  {m : ℂ}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (h : ℤ)
  (hk : k ≤ ts.length) :
-- imply
  (midsAux m h ts)[k]? = some (hexInfra_midAccum m h (ts.take k)) := by
-- proof
  apply StatMech.Universality.hexJordan_midsAux_getElem m h ts k hk

/--
[hexJordan_verticesAux_getElem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_verticesAux_getElem_eq
  {m : ℂ}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (h : ℤ)
  (hk : k ≤ ts.length) :
-- imply
  (verticesAux m h ts)[k]? = some (hexInfra_midAccum m h (ts.take k) + halfStep (hexInfra_headAccum h (ts.take k))) := by
-- proof
  apply StatMech.Universality.hexJordan_verticesAux_getElem m h ts k hk

/--
[hexJordan_vertexPos_ne_of_saw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_vertexPos_ne_of_saw_eq
  {a : ℂ}
  {ts : List ℤ}
  {i j : ℕ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 ts).IsSAW)
  (hi : i ≤ ts.length)
  (hj : j ≤ ts.length)
  (hne : i ≠ j) :
-- imply
  hexJordan_vertexPos a h0 ts i ≠ hexJordan_vertexPos a h0 ts j := by
-- proof
  apply StatMech.Universality.hexJordan_vertexPos_ne_of_saw a h0 ts hsaw i j hi hj hne

/--
[hexJordan_sum_hexUnit_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_sum_hexUnit_six_eq
-- given
  (h : ℤ) :
-- imply
  hexUnit h + hexUnit (h + 1) + hexUnit (h + 2) + hexUnit (h + 3) + hexUnit (h + 4) + hexUnit (h + 5) = 0 := by
-- proof
  apply StatMech.Universality.hexJordan_sum_hexUnit_six h

/--
[hexJordan_midAccum_six_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_midAccum_six_left_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_midAccum a h0 [(1 : ℤ), 1, 1, 1, 1, 1] = a := by
-- proof
  apply StatMech.Universality.hexJordan_midAccum_six_left a h0

/--
[hexJordan_midAccum_six_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_midAccum_six_right_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_midAccum a h0 [(-1 : ℤ), -1, -1, -1, -1, -1] = a := by
-- proof
  apply StatMech.Universality.hexJordan_midAccum_six_right a h0

/--
[hexJordan_headAccum_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_headAccum_append_eq
  {s t : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_headAccum h (s ++ t) = hexInfra_headAccum (hexInfra_headAccum h s) t := by
-- proof
  apply StatMech.Universality.hexJordan_headAccum_append h s t

/--
[hexJordan_midAccum_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_midAccum_append_eq
  {m : ℂ}
  {s t : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_midAccum m h (s ++ t) = hexInfra_midAccum (hexInfra_midAccum m h s) (hexInfra_headAccum h s) t := by
-- proof
  apply StatMech.Universality.hexJordan_midAccum_append m h s t

/--
[hexJordan_no_revolution_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_no_revolution_pair_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 ts).IsSAW)
  (hclose : ∀ i j, i ≤ ts.length → j ≤ ts.length → hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6 → hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j) :
-- imply
  ∀ i j, i ≤ ts.length → j ≤ ts.length → hexStripWinding_runningHead h0 ts j ≠ hexStripWinding_runningHead h0 ts i + 6 := by
-- proof
  apply StatMech.Universality.hexJordan_no_revolution_pair a h0 ts hsaw hclose

/--
[hexJordan_span_lt_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_span_lt_six_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).IsLegalSAW)
  (hno6 : ∀ i j, i ≤ ts.length → j ≤ ts.length → hexStripWinding_runningHead h0 ts j ≠ hexStripWinding_runningHead h0 ts i + 6) :
-- imply
  ∀ i j, i ≤ ts.length → j ≤ ts.length → |hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j| < 6 := by
-- proof
  apply StatMech.Universality.hexJordan_span_lt_six a h0 ts hlegal hno6

/--
[hexJordan_window_of_span_attained](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_window_of_span_attained_eq
  {ts : List ℤ}
  {p : ℕ}
-- given
  (h0 w : ℤ)
  (hspan : ∀ i j, i ≤ ts.length → j ≤ ts.length → |hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j| < 6)
  (hp : p ≤ ts.length)
  (hpw : hexStripWinding_runningHead h0 ts p = w)
  (hfloor : ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k) :
-- imply
  (∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k) ∧ (∀ k, k ≤ ts.length → hexStripWinding_runningHead h0 ts k ≠ w + 6) := by
-- proof
  apply StatMech.Universality.hexJordan_window_of_span_attained h0 w ts hspan p hp hpw hfloor

/--
[wallField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma wallField_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hk : k ≤ ts.length) :
-- imply
  B.w ≤ hexStripWinding_runningHead h0 ts k := by
-- proof
  apply StatMech.Universality.HexStripSimplyConnected.wallField ts hadm k hk

/--
[noFullTurnField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma noFullTurnField_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hk : k ≤ ts.length) :
-- imply
  hexStripWinding_runningHead h0 ts k ≠ B.w + 6 := by
-- proof
  apply StatMech.Universality.HexStripSimplyConnected.noFullTurnField ts hadm k hk

/--
[spanField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma spanField_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {ts : List ℤ}
  {i j : ℕ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hi : i ≤ ts.length)
  (hj : j ≤ ts.length) :
-- imply
  |hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j| < 6 := by
-- proof
  apply StatMech.Universality.HexStripSimplyConnected.spanField ts hadm i j hi hj

/--
[hexJordan_toStripBand_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_toStripBand_H_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripSimplyConnected inRegion a h0 z}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  (hexJordan_toStripBand inRegion a h0 z B).H = B.H := by
-- proof
  apply StatMech.Universality.hexJordan_toStripBand_H inRegion a h0 z B

/--
[hexJordan_toStripBand_w](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_toStripBand_w_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripSimplyConnected inRegion a h0 z}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  (hexJordan_toStripBand inRegion a h0 z B).w = B.w := by
-- proof
  apply StatMech.Universality.hexJordan_toStripBand_w inRegion a h0 z B

/--
[hexJordan_stripWinding_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_stripWinding_H_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripSimplyConnected inRegion a h0 z}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  (hexJordan_stripWinding inRegion a h0 z B).H = B.H := by
-- proof
  apply StatMech.Universality.hexJordan_stripWinding_H inRegion a h0 z B

/--
[hexJordan_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_bound_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripSimplyConnected inRegion a h0 z}
  {ts : List ℤ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  |hexInfra_headAccum h0 ts - B.H| < 6 := by
-- proof
  apply StatMech.Universality.hexJordan_bound inRegion a h0 z B ts hadm

/--
[hexJordan_six_left_not_saw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_six_left_not_saw_eq
  {a : ℂ}
  {s r : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 (s ++ ([(1 : ℤ), 1, 1, 1, 1, 1] ++ r))).IsSAW) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.hexJordan_six_left_not_saw a h0 s r hsaw

/--
[hexJordan_six_right_not_saw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_six_right_not_saw_eq
  {a : ℂ}
  {s r : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 (s ++ ([(-1 : ℤ), -1, -1, -1, -1, -1] ++ r))).IsSAW) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.hexJordan_six_right_not_saw a h0 s r hsaw

/--
[hexJordan_simplyConnected_trivial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean)
-/
@[path]
private lemma hexJordan_simplyConnected_trivial_bound_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  |hexInfra_headAccum h0 ([] : List ℤ) - (hexJordan_simplyConnected_trivial a h0).H| < 6 := by
-- proof
  apply StatMech.Universality.hexJordan_simplyConnected_trivial_bound a h0


-- created on 2026-10-23
