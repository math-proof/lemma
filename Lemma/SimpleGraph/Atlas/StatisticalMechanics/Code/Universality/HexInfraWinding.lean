import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
open StatMech StatMech.Universality


/--
[hexInfra_headAccum_eq_add_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_headAccum_eq_add_sum_eq
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_headAccum h ts = h + ts.sum := by
-- proof
  apply StatMech.Universality.hexInfra_headAccum_eq_add_sum h ts

/--
[hexInfra_turning_eq_headAccum_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_turning_eq_headAccum_sub_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((hexInfra_headAccum h0 ts : ℝ) - (h0 : ℝ)) := by
-- proof
  apply StatMech.Universality.hexInfra_turning_eq_headAccum_sub a h0 ts

/--
[hexInfra_turning_const_of_finalHeading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_turning_const_of_finalHeading_eq
  {a : ℂ}
  {ts : List ℤ}
  {H : ℤ}
-- given
  (h0 : ℤ)
  (hH : hexInfra_headAccum h0 ts = H) :
-- imply
  (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((H : ℝ) - (h0 : ℝ)) := by
-- proof
  apply StatMech.Universality.hexInfra_turning_const_of_finalHeading a h0 ts H hH

/--
[hexInfra_turning_eq_of_finalHeading_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_turning_eq_of_finalHeading_eq_eq
  {a a' : ℂ}
  {ts ts' : List ℤ}
-- given
  (h0 : ℤ)
  (hh : hexInfra_headAccum h0 ts = hexInfra_headAccum h0 ts') :
-- imply
  (HexWalk.ofTurns a h0 ts).turning = (HexWalk.ofTurns a' h0 ts').turning := by
-- proof
  apply StatMech.Universality.hexInfra_turning_eq_of_finalHeading_eq a a' h0 ts ts' hh

/--
[hexInfra_midsAux_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_midsAux_getLast_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (HexWalk.midsAux m h ts).getLast? = some (hexInfra_midAccum m h ts) := by
-- proof
  apply StatMech.Universality.hexInfra_midsAux_getLast m h ts

/--
[hexInfra_endMid_eq_midAccum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_endMid_eq_midAccum_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 ts).endMid = hexInfra_midAccum a h0 ts := by
-- proof
  apply StatMech.Universality.hexInfra_endMid_eq_midAccum a h0 ts

/--
[hexInfra_det_winding_of_finalHeading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_det_winding_of_finalHeading_eq
  {a : ℂ}
  {z : ℂ}
  {H : ℤ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hfh : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → hexInfra_headAccum h0 ts = H) :
-- imply
  ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((H : ℝ) - (h0 : ℝ)) := by
-- proof
  apply StatMech.Universality.hexInfra_det_winding_of_finalHeading inRegion a h0 z H hfh

/--
[hexInfra_topSide_finalHeading_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_topSide_finalHeading_zero_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hH : hexInfra_headAccum h0 ts = h0) :
-- imply
  (HexWalk.ofTurns a h0 ts).turning = 0 := by
-- proof
  apply StatMech.Universality.hexInfra_topSide_finalHeading_zero a h0 ts hH

/--
[hexInfra_trivial_finalHeading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_trivial_finalHeading_eq
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_headAccum h0 ([] : List ℤ) = h0 := by
-- proof
  apply StatMech.Universality.hexInfra_trivial_finalHeading h0

/--
[hexInfra_singleRight_finalHeading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_singleRight_finalHeading_eq
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_headAccum h0 [(-1 : ℤ)] = h0 - 1 := by
-- proof
  apply StatMech.Universality.hexInfra_singleRight_finalHeading h0

/--
[hexInfra_singleRight_turning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraWinding.lean)
-/
@[path]
private lemma hexInfra_singleRight_turning_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 [(-1 : ℤ)]).turning = -(Real.pi / 3) := by
-- proof
  apply StatMech.Universality.hexInfra_singleRight_turning a h0


-- created on 2026-10-23
