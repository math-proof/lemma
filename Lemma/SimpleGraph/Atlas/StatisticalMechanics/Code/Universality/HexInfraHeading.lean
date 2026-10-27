import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
open StatMech StatMech.Universality


/--
[hexUnit_add_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexUnit_add_six_eq
-- given
  (h : ℤ) :
-- imply
  hexUnit (h + 6) = hexUnit h := by
-- proof
  apply StatMech.Universality.hexUnit_add_six h

/--
[hexUnit_eq_iff_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexUnit_eq_iff_mod_eq
-- given
  (h h' : ℤ) :
-- imply
  hexUnit h = hexUnit h' ↔ (6 : ℤ) ∣ (h - h') := by
-- proof
  apply StatMech.Universality.hexUnit_eq_iff_mod h h'

/--
[hexInfra_halfStep_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexInfra_halfStep_inj_eq
  {h h' : ℤ}
-- given
  (he : HexWalk.halfStep h = HexWalk.halfStep h') :
-- imply
  hexUnit h = hexUnit h' := by
-- proof
  apply StatMech.Universality.hexInfra_halfStep_inj he

/--
[hexInfra_lastVertex_eq_endMid_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexInfra_lastVertex_eq_endMid_add_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts) = (HexWalk.ofTurns a h0 ts).endMid + HexWalk.halfStep (hexInfra_headAccum h0 ts) := by
-- proof
  apply StatMech.Universality.hexInfra_lastVertex_eq_endMid_add a h0 ts

/--
[hexInfra_lastVertex_sub_endMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexInfra_lastVertex_sub_endMid_eq
  {a : ℂ}
  {z : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hz : (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)) - z = HexWalk.halfStep (hexInfra_headAccum h0 ts) := by
-- proof
  apply StatMech.Universality.hexInfra_lastVertex_sub_endMid a h0 z ts hz

/--
[hexInfra_finalHeading_mod_of_lastVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexInfra_finalHeading_mod_of_lastVertex_eq
  {a : ℂ}
  {z : ℂ}
  {H : ℤ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hz : (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hv : hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts) = z + HexWalk.halfStep H) :
-- imply
  (6 : ℤ) ∣ (hexInfra_headAccum h0 ts - H) := by
-- proof
  apply StatMech.Universality.hexInfra_finalHeading_mod_of_lastVertex a h0 z H ts hz hv

/--
[hexInfra_finalHeading_eq_of_lastVertex_of_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexInfra_finalHeading_eq_of_lastVertex_of_range_eq
  {a : ℂ}
  {z : ℂ}
  {H w : ℤ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hz : (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hv : hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts) = z + HexWalk.halfStep H)
  (hwinL : w ≤ hexInfra_headAccum h0 ts)
  (hwinU : hexInfra_headAccum h0 ts < w + 6)
  (hHL : w ≤ H)
  (hHU : H < w + 6) :
-- imply
  hexInfra_headAccum h0 ts = H := by
-- proof
  apply StatMech.Universality.hexInfra_finalHeading_eq_of_lastVertex_of_range a h0 z H w ts hz hv hwinL hwinU hHL hHU

/--
[hexInfra_det_winding_of_directedHalfEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexInfra_det_winding_of_directedHalfEdge_eq
  {a : ℂ}
  {z : ℂ}
  {H w : ℤ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hz : (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hv : hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts) = z + HexWalk.halfStep H)
  (hwinL : w ≤ hexInfra_headAccum h0 ts)
  (hwinU : hexInfra_headAccum h0 ts < w + 6)
  (hHL : w ≤ H)
  (hHU : H < w + 6) :
-- imply
  (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((H : ℝ) - (h0 : ℝ)) := by
-- proof
  apply StatMech.Universality.hexInfra_det_winding_of_directedHalfEdge a h0 z H w ts hz hv hwinL hwinU hHL hHU

/--
[hexInfra_trivial_lastVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexInfra_trivial_lastVertex_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_midAccum a h0 ([] : List ℤ) + HexWalk.halfStep (hexInfra_headAccum h0 []) = a + HexWalk.halfStep h0 := by
-- proof
  apply StatMech.Universality.hexInfra_trivial_lastVertex a h0

/--
[hexInfra_trivial_directedHalfEdge_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexInfra_trivial_directedHalfEdge_heading_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_headAccum h0 ([] : List ℤ) = h0 := by
-- proof
  apply StatMech.Universality.hexInfra_trivial_directedHalfEdge_heading a h0

/--
[hexInfra_trivial_directedHalfEdge_turning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexInfra_trivial_directedHalfEdge_turning_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 ([] : List ℤ)).turning = 0 := by
-- proof
  apply StatMech.Universality.hexInfra_trivial_directedHalfEdge_turning a h0

/--
[hexInfra_singleRight_finalHeading_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraHeading.lean)
-/
@[path]
private lemma hexInfra_singleRight_finalHeading_mod_eq :
-- imply
  (6 : ℤ) ∣ (hexInfra_headAccum 0 [(-1 : ℤ)] - (-1)) := by
-- proof
  apply StatMech.Universality.hexInfra_singleRight_finalHeading_mod


-- created on 2026-10-23
