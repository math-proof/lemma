import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexNoFullSweepClose.Part5
open StatMech StatMech.Universality StatMech.Universality.HexStripSimplyConnectedMonotone


/--
[hexSweep_runningHead_eq_of_monotone_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_runningHead_eq_of_monotone_up_eq
  {ts : List ℤ}
  {i j : ℕ}
-- given
  (h0 : ℤ)
  (hij : i ≤ j)
  (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = 1)
  (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6) :
-- imply
  j = i + 6 := by
-- proof
  apply StatMech.Universality.hexSweep_runningHead_eq_of_monotone_up h0 ts i j hij hmono hsweep

/--
[hexSweep_runningHead_eq_of_monotone_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_runningHead_eq_of_monotone_down_eq
  {ts : List ℤ}
  {i j : ℕ}
-- given
  (h0 : ℤ)
  (hij : i ≤ j)
  (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = -1)
  (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i - 6) :
-- imply
  j = i + 6 := by
-- proof
  apply StatMech.Universality.hexSweep_runningHead_eq_of_monotone_down h0 ts i j hij hmono hsweep

/--
[hexSweep_segment_eq_six_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_segment_eq_six_left_eq
  {ts : List ℤ}
  {i : ℕ}
-- given
  (hlen : i + 6 ≤ ts.length)
  (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = 1) :
-- imply
  (ts.drop i).take 6 = [(1 : ℤ), 1, 1, 1, 1, 1] := by
-- proof
  apply StatMech.Universality.hexSweep_segment_eq_six_left ts i hlen hmono

/--
[hexSweep_segment_eq_six_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_segment_eq_six_right_eq
  {ts : List ℤ}
  {i : ℕ}
-- given
  (hlen : i + 6 ≤ ts.length)
  (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = -1) :
-- imply
  (ts.drop i).take 6 = [(-1 : ℤ), -1, -1, -1, -1, -1] := by
-- proof
  apply StatMech.Universality.hexSweep_segment_eq_six_right ts i hlen hmono

/--
[hexSweep_vertexPos_eq_of_six_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_vertexPos_eq_of_six_left_eq
  {a : ℂ}
  {ts : List ℤ}
  {i : ℕ}
-- given
  (h0 : ℤ)
  (hlen : i + 6 ≤ ts.length)
  (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = 1) :
-- imply
  hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts (i + 6) := by
-- proof
  apply StatMech.Universality.hexSweep_vertexPos_eq_of_six_left a h0 ts i hlen hmono

/--
[hexSweep_vertexPos_eq_of_six_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_vertexPos_eq_of_six_right_eq
  {a : ℂ}
  {ts : List ℤ}
  {i : ℕ}
-- given
  (h0 : ℤ)
  (hlen : i + 6 ≤ ts.length)
  (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = -1) :
-- imply
  hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts (i + 6) := by
-- proof
  apply StatMech.Universality.hexSweep_vertexPos_eq_of_six_right a h0 ts i hlen hmono

/--
[hexSweep_vertexPos_eq_of_monotone_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_vertexPos_eq_of_monotone_up_eq
  {a : ℂ}
  {ts : List ℤ}
  {i j : ℕ}
-- given
  (h0 : ℤ)
  (hij : i ≤ j)
  (hj : j ≤ ts.length)
  (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = 1)
  (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6) :
-- imply
  hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j := by
-- proof
  apply StatMech.Universality.hexSweep_vertexPos_eq_of_monotone_up a h0 ts i j hij hj hmono hsweep

/--
[hexSweep_vertexPos_eq_of_monotone_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_vertexPos_eq_of_monotone_down_eq
  {a : ℂ}
  {ts : List ℤ}
  {i j : ℕ}
-- given
  (h0 : ℤ)
  (hij : i ≤ j)
  (hj : j ≤ ts.length)
  (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = -1)
  (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i - 6) :
-- imply
  hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j := by
-- proof
  apply StatMech.Universality.hexSweep_vertexPos_eq_of_monotone_down a h0 ts i j hij hj hmono hsweep

/--
[noFullSweepField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma noFullSweepField_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {ts : List ℤ}
  {i j : ℕ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hi : i ≤ ts.length)
  (hj : j ≤ ts.length)
  (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6) :
-- imply
  hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j := by
-- proof
  apply StatMech.Universality.HexStripSimplyConnectedMonotone.noFullSweepField ts hadm i j hi hj hsweep

/--
[hexSweep_toSimplyConnected_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_toSimplyConnected_H_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripSimplyConnectedMonotone inRegion a h0 z}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  (hexSweep_toSimplyConnected inRegion a h0 z B).H = B.H := by
-- proof
  apply StatMech.Universality.hexSweep_toSimplyConnected_H inRegion a h0 z B

/--
[hexSweep_toSimplyConnected_w](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_toSimplyConnected_w_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripSimplyConnectedMonotone inRegion a h0 z}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  (hexSweep_toSimplyConnected inRegion a h0 z B).w = B.w := by
-- proof
  apply StatMech.Universality.hexSweep_toSimplyConnected_w inRegion a h0 z B

/--
[hexSweep_stripWinding_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_stripWinding_H_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripSimplyConnectedMonotone inRegion a h0 z}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  (hexSweep_stripWinding inRegion a h0 z B).H = B.H := by
-- proof
  apply StatMech.Universality.hexSweep_stripWinding_H inRegion a h0 z B

/--
[hexSweep_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_bound_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripSimplyConnectedMonotone inRegion a h0 z}
  {ts : List ℤ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  |hexInfra_headAccum h0 ts - B.H| < 6 := by
-- proof
  apply StatMech.Universality.hexSweep_bound inRegion a h0 z B ts hadm

/--
[hexSweep_simplyConnected_trivial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_simplyConnected_trivial_bound_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  |hexInfra_headAccum h0 ([] : List ℤ) - (hexSweep_simplyConnected_trivial a h0).H| < 6 := by
-- proof
  apply StatMech.Universality.hexSweep_simplyConnected_trivial_bound a h0

/--
[hexSweep_six_left_not_saw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_six_left_not_saw_eq
  {a : ℂ}
  {s r : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 (s ++ ([(1 : ℤ), 1, 1, 1, 1, 1] ++ r))).IsSAW) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.hexSweep_six_left_not_saw a h0 s r hsaw

/--
[hexSweep_nonMonotone_revolution_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean)
-/
@[path]
private lemma hexSweep_nonMonotone_revolution_pair_eq
-- given
  (h0 : ℤ) :
-- imply
  hexStripWinding_runningHead h0 [(1 : ℤ), 1, 1, 1, 1, 1, 1, -1] 8 = hexStripWinding_runningHead h0 [(1 : ℤ), 1, 1, 1, 1, 1, 1, -1] 0 + 6 := by
-- proof
  apply StatMech.Universality.hexSweep_nonMonotone_revolution_pair h0


-- created on 2026-10-23
