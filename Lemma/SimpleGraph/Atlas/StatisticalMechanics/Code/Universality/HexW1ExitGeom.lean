import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexW1ExitGeom
open StatMech StatMech.Universality StatMech.Universality.HexStraightSide


/--
[hexW1Exit_halfStep_add_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_halfStep_add_three_eq
-- given
  (h : ℤ) :
-- imply
  HexWalk.halfStep (h + 3) = - HexWalk.halfStep h := by
-- proof
  apply StatMech.Universality.hexW1Exit_halfStep_add_three h

/--
[hexW1Exit_penult_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_penult_mem_eq
  {m : ℂ}
  {t : ℤ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_midAccum m h (t :: ts) - HexWalk.halfStep (hexInfra_headAccum h (t :: ts)) ∈ HexWalk.verticesAux m h (t :: ts) := by
-- proof
  apply StatMech.Universality.hexW1Exit_penult_mem m h t ts

/--
[hexW1Exit_halfStep_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_halfStep_ne_zero_eq
-- given
  (h : ℤ) :
-- imply
  HexWalk.halfStep h ≠ 0 := by
-- proof
  apply StatMech.Universality.hexW1Exit_halfStep_ne_zero h

/--
[hexW1Exit_penult_eq_of_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_penult_eq_of_endsAt_eq
  {a : ℂ}
  {z : ℂ}
  {t : ℤ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hz : (HexWalk.ofTurns a h0 (t :: ts)).EndsAt z) :
-- imply
  z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts)) ∈ (HexWalk.ofTurns a h0 (t :: ts)).vertices := by
-- proof
  apply StatMech.Universality.hexW1Exit_penult_eq_of_endsAt a h0 z t ts hz

/--
[hexW1Exit_penult_ne_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_penult_ne_last_eq
  {z : ℂ}
  {H : ℤ} :
-- imply
  z - HexWalk.halfStep H ≠ z + HexWalk.halfStep H := by
-- proof
  apply StatMech.Universality.hexW1Exit_penult_ne_last z H

/--
[hexW1Exit_lastVertex_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_lastVertex_eq_iff_eq
  {a : ℂ}
  {z : ℂ}
  {H : ℤ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hz : (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts) = z + HexWalk.halfStep H) ↔ HexWalk.halfStep (hexInfra_headAccum h0 ts) = HexWalk.halfStep H := by
-- proof
  apply StatMech.Universality.hexW1Exit_lastVertex_eq_iff a h0 z H ts hz

/--
[hexW1Exit_lastVertex_of_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_lastVertex_of_dir_eq
  {a : ℂ}
  {z : ℂ}
  {H : ℤ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hz : (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hdir : HexWalk.halfStep (hexInfra_headAccum h0 ts) = HexWalk.halfStep H) :
-- imply
  hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts) = z + HexWalk.halfStep H := by
-- proof
  apply StatMech.Universality.hexW1Exit_lastVertex_of_dir a h0 z H ts hz hdir

/--
[dir_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma dir_eq_eq
  {inRegion interior : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {t : ℤ}
  {ts : List ℤ}
-- given
  (hadm : (HexWalk.ofTurns a h0 (t :: ts)).IsLegalSAW ∧ (HexWalk.ofTurns a h0 (t :: ts)).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 (t :: ts)).EndsAt z) :
-- imply
  HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts)) = HexWalk.halfStep S.H := by
-- proof
  apply StatMech.Universality.HexStraightSide.dir_eq t ts hadm

/--
[side_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma side_exit_eq
  {inRegion interior : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {t : ℤ}
  {ts : List ℤ}
-- given
  (hadm : (HexWalk.ofTurns a h0 (t :: ts)).IsLegalSAW ∧ (HexWalk.ofTurns a h0 (t :: ts)).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 (t :: ts)).EndsAt z) :
-- imply
  hexInfra_midAccum a h0 (t :: ts) + HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts)) = z + HexWalk.halfStep S.H := by
-- proof
  apply StatMech.Universality.HexStraightSide.side_exit t ts hadm

/--
[hexW1Exit_singleton_uniqueInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_singleton_uniqueInterior_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (h : ℤ)
  (hint : (fun m => m = a + HexWalk.halfStep h0) (a + HexWalk.halfStep h)) :
-- imply
  HexWalk.halfStep h = HexWalk.halfStep ((h0 + 3) + 3) := by
-- proof
  apply StatMech.Universality.hexW1Exit_singleton_uniqueInterior a h0 h hint

/--
[hexW1Exit_singleton_inner_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_singleton_inner_eq_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  a - HexWalk.halfStep ((h0 + 3 : ℤ)) = a + HexWalk.halfStep h0 := by
-- proof
  apply StatMech.Universality.hexW1Exit_singleton_inner_eq a h0

/--
[hexW1Exit_mids_singleRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_mids_singleRight_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 [(-1 : ℤ)]).mids = [a, a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))] := by
-- proof
  apply StatMech.Universality.hexW1Exit_mids_singleRight a h0

/--
[hexW1Exit_singleRight_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_singleRight_legal_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 [(-1 : ℤ)]).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexW1Exit_singleRight_legal a h0

/--
[hexW1Exit_singleRight_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_singleRight_endsAt_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 [(-1 : ℤ)]).EndsAt (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) := by
-- proof
  apply StatMech.Universality.hexW1Exit_singleRight_endsAt a h0

/--
[hexW1Exit_singleRight_staysIn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_singleRight_staysIn_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn (fun m => m = a ∨ m = a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) := by
-- proof
  apply StatMech.Universality.hexW1Exit_singleRight_staysIn a h0

/--
[hexW1Exit_singleRight_dir_eq_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_singleRight_dir_eq_fires_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (inReg : ℂ → Prop)
  (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg ∧ (HexWalk.ofTurns a h0 ts).EndsAt (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
  (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
-- imply
  HexWalk.halfStep (hexInfra_headAccum h0 [(-1 : ℤ)]) = HexWalk.halfStep ((hexW1Exit_singleRight_straightSide a h0 inReg hclass).H) := by
-- proof
  apply StatMech.Universality.hexW1Exit_singleRight_dir_eq_fires a h0 inReg hclass hstay

/--
[hexW1Exit_singleRight_side_exit_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean)
-/
@[path]
private lemma hexW1Exit_singleRight_side_exit_fires_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (inReg : ℂ → Prop)
  (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg ∧ (HexWalk.ofTurns a h0 ts).EndsAt (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
  (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
-- imply
  hexInfra_midAccum a h0 [(-1 : ℤ)] + HexWalk.halfStep (hexInfra_headAccum h0 [(-1 : ℤ)]) = (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) + HexWalk.halfStep ((hexW1Exit_singleRight_straightSide a h0 inReg hclass).H) := by
-- proof
  apply StatMech.Universality.hexW1Exit_singleRight_side_exit_fires a h0 inReg hclass hstay


-- created on 2026-10-23
