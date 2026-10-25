import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
open StatMech StatMech.Universality StatMech.Universality.HexReturnCoord


/--
[value_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma value_zero_eq :
-- imply
  zero.value = 0 := by
-- proof
  apply StatMech.Universality.HexReturnCoord.value_zero

/--
[value_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma value_base_eq :
-- imply
  base.value = 1 := by
-- proof
  apply StatMech.Universality.HexReturnCoord.value_base

/--
[value_negBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma value_negBase_eq :
-- imply
  negBase.value = -1 := by
-- proof
  apply StatMech.Universality.HexReturnCoord.value_negBase

/--
[value_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma value_add_eq
  {d e : HexReturnCoord} :
-- imply
  (d.add e).value = d.value + e.value := by
-- proof
  apply StatMech.Universality.HexReturnCoord.value_add d e

/--
[value_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma value_left_eq
  {d : HexReturnCoord} :
-- imply
  d.left.value = -(hexOmega ^ 2 * d.value) := by
-- proof
  apply StatMech.Universality.HexReturnCoord.value_left d

/--
[value_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma value_right_eq
  {d : HexReturnCoord} :
-- imply
  d.right.value = -(hexOmega * d.value) := by
-- proof
  apply StatMech.Universality.HexReturnCoord.value_right d

/--
[base_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma base_isUnit_eq :
-- imply
  base.IsUnit := by
-- proof
  apply StatMech.Universality.HexReturnCoord.base_isUnit

/--
[isUnit_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma isUnit_turn_eq
  {d : HexReturnCoord}
  {t : ℤ}
-- given
  (hd : d.IsUnit)
  (ht : t = 1 ∨ t = -1) :
-- imply
  (d.turn t).IsUnit := by
-- proof
  apply StatMech.Universality.HexReturnCoord.isUnit_turn hd ht

/--
[hexReturnState_direction_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma hexReturnState_direction_isUnit_eq
  {d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hd : d.IsUnit)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  (hexReturnState d ts).direction.IsUnit := by
-- proof
  apply StatMech.Universality.hexReturnState_direction_isUnit d ts hd hlegal

/--
[hexReturnState_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma hexReturnState_parity_eq
  {d : HexReturnCoord}
  {ts : List ℤ} :
-- imply
  (2 : ℤ) ∣ (hexReturnState d ts).displacement.x - d.x - (hexReturnState d ts).direction.x ∧ (2 : ℤ) ∣ (hexReturnState d ts).displacement.y - d.y - (hexReturnState d ts).direction.y := by
-- proof
  apply StatMech.Universality.hexReturnState_parity d ts

/--
[hexReturnState_direction_eq_base_or_negBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma hexReturnState_direction_eq_base_or_negBase_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hzero : (hexReturnState HexReturnCoord.base ts).displacement = HexReturnCoord.zero) :
-- imply
  (hexReturnState HexReturnCoord.base ts).direction = HexReturnCoord.base ∨ (hexReturnState HexReturnCoord.base ts).direction = HexReturnCoord.negBase := by
-- proof
  apply StatMech.Universality.hexReturnState_direction_eq_base_or_negBase ts hlegal hzero

/--
[hexReturn_halfStep_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma hexReturn_halfStep_turn_eq
  {s : ℂ}
  {d : HexReturnCoord}
  {t : ℤ}
-- given
  (h : ℤ)
  (hdir : halfStep h = d.value * s)
  (ht : t = 1 ∨ t = -1) :
-- imply
  halfStep (h + t) = (d.turn t).value * s := by
-- proof
  apply StatMech.Universality.hexReturn_halfStep_turn s h d t hdir ht

/--
[hexReturnState_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma hexReturnState_geometry_eq
  {s m : ℂ}
  {d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (h : ℤ)
  (hdir : halfStep h = d.value * s)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  hexInfra_midAccum m h ts = m + (hexReturnState d ts).displacement.value * s ∧ halfStep (hexInfra_headAccum h ts) = (hexReturnState d ts).direction.value * s := by
-- proof
  apply StatMech.Universality.hexReturnState_geometry s m h d ts hdir hlegal

/--
[hexReturnCoord_value_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma hexReturnCoord_value_eq_zero_eq
  {d : HexReturnCoord}
-- given
  (h : d.value = 0) :
-- imply
  d = HexReturnCoord.zero := by
-- proof
  apply StatMech.Universality.hexReturnCoord_value_eq_zero h

/--
[hexReturning_finalDirection_parallel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma hexReturning_finalDirection_parallel_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).LegalTurns)
  (hend : (ofTurns a h0 ts).EndsAt a) :
-- imply
  halfStep (hexInfra_headAccum h0 ts) = halfStep h0 ∨ halfStep (hexInfra_headAccum h0 ts) = -halfStep h0 := by
-- proof
  apply StatMech.Universality.hexReturning_finalDirection_parallel a h0 ts hlegal hend

/--
[hexReturn_eq_nil_of_lastVertex_eq_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma hexReturn_eq_nil_of_lastVertex_eq_first_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 ts).IsSAW)
  (hlast : hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) = a + halfStep h0) :
-- imply
  ts = [] := by
-- proof
  apply StatMech.Universality.hexReturn_eq_nil_of_lastVertex_eq_first a h0 ts hsaw hlast

/--
[hexReturningLegalSAW_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean)
-/
@[path]
private lemma hexReturningLegalSAW_eq_nil_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).IsLegalSAW)
  (hend : (ofTurns a h0 ts).EndsAt a) :
-- imply
  ts = [] := by
-- proof
  apply StatMech.Universality.hexReturningLegalSAW_eq_nil a h0 ts hlegal hend


-- created on 2026-10-23
