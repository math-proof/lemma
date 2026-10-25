import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part5
open StatMech StatMech.Universality


/--
[hexStripDirMids_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStripDirMids_nil_eq
  {m : ℂ}
-- given
  (h : ℤ) :
-- imply
  hexStripDirMids m h [] = [(m, h)] := by
-- proof
  apply StatMech.Universality.hexStripDirMids_nil m h

/--
[hexStripDirMids_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStripDirMids_cons_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  hexStripDirMids m h (t :: ts) = (m, h) :: hexStripDirMids (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) ts := by
-- proof
  apply StatMech.Universality.hexStripDirMids_cons m h t ts

/--
[hexStrip_nonlast_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_nonlast_dir_eq
  {m : ℂ}
  {ts : List ℤ}
  {v : ℂ}
-- given
  (h : ℤ)
  (hv : v ∈ HexWalk.verticesAux m h ts)
  (hvne : v ≠ hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)) :
-- imply
  ∃ (m' : ℂ) (h' t' : ℤ), (m', h') ∈ hexStripDirMids m h ts ∧ (m' + HexWalk.halfStep h' + HexWalk.halfStep (h' + t'), h' + t') ∈ hexStripDirMids m h ts ∧ v = m' + HexWalk.halfStep h' ∧ t' ∈ ts := by
-- proof
  apply StatMech.Universality.hexStrip_nonlast_dir m h ts v hv hvne

/--
[hexStrip_interiorVertices_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_interiorVertices_core_eq
  {a : ℂ}
  {ts : List ℤ}
  {v : ℂ}
-- given
  (dregion : ℂ → ℤ → Prop)
  (h0 : ℤ)
  (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW)
  (hstay : hexStripStaysInDir dregion a h0 ts)
  (hv : v ∈ (HexWalk.ofTurns a h0 ts).vertices)
  (hvne : v ≠ hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)) :
-- imply
  hexStripInterior dregion v := by
-- proof
  apply StatMech.Universality.hexStrip_interiorVertices_core dregion a h0 ts hlegal hstay v hv hvne

/--
[hexStrip_halfStep_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_halfStep_re_eq
-- given
  (h : ℤ) :
-- imply
  (HexWalk.halfStep h).re = (1 / 2) * Real.cos (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
-- proof
  apply StatMech.Universality.hexStrip_halfStep_re h

/--
[hexStrip_halfStep_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_halfStep_im_eq
-- given
  (h : ℤ) :
-- imply
  (HexWalk.halfStep h).im = (1 / 2) * Real.sin (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
-- proof
  apply StatMech.Universality.hexStrip_halfStep_im h

/--
[hexStrip_normSq_halfStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_normSq_halfStep_eq
-- given
  (h : ℤ) :
-- imply
  Complex.normSq (HexWalk.halfStep h) = 1 / 4 := by
-- proof
  apply StatMech.Universality.hexStrip_normSq_halfStep h

/--
[hexStrip_normSq_two_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_normSq_two_one_eq
-- given
  (h0 : ℤ) :
-- imply
  Complex.normSq (2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) = 7 / 4 := by
-- proof
  apply StatMech.Universality.hexStrip_normSq_two_one h0

/--
[hexStrip_two_one_add_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_two_one_add_ne_zero_eq
-- given
  (h0 h : ℤ) :
-- imply
  2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) + HexWalk.halfStep h ≠ 0 := by
-- proof
  apply StatMech.Universality.hexStrip_two_one_add_ne_zero h0 h

/--
[hexStrip_outer_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_outer_ne_eq
  {a : ℂ}
-- given
  (h0 h : ℤ) :
-- imply
  a + HexWalk.halfStep (h0 + 3) ≠ (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) + HexWalk.halfStep h := by
-- proof
  apply StatMech.Universality.hexStrip_outer_ne a h0 h

/--
[hexStrip_singleRight_dirMids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_singleRight_dirMids_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexStripDirMids a h0 [(-1 : ℤ)] = [(a, h0), (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)), h0 + (-1))] := by
-- proof
  apply StatMech.Universality.hexStrip_singleRight_dirMids a h0

/--
[hexStrip_singleRight_staysInDir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_singleRight_staysInDir_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexStripStaysInDir (hexStrip_singleRightDReg a h0) a h0 [(-1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hexStrip_singleRight_staysInDir a h0

/--
[hexStrip_singleRight_interior_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_singleRight_interior_fires_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexStripInterior (hexStrip_singleRightDReg a h0) (a + HexWalk.halfStep h0) := by
-- proof
  apply StatMech.Universality.hexStrip_singleRight_interior_fires a h0

/--
[hexStrip_singleRight_uniqueInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_singleRight_uniqueInterior_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (h : ℤ)
  (hint : hexStripInterior (hexStrip_singleRightDReg a h0) ((a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) + HexWalk.halfStep h)) :
-- imply
  HexWalk.halfStep h = HexWalk.halfStep ((h0 - 1) + 3) := by
-- proof
  apply StatMech.Universality.hexStrip_singleRight_uniqueInterior a h0 h hint

/--
[hexStrip_singleRight_side_exit_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean)
-/
@[path]
private lemma hexStrip_singleRight_side_exit_fires_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (inReg : ℂ → Prop)
  (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg ∧ (HexWalk.ofTurns a h0 ts).EndsAt (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
  (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
-- imply
  hexInfra_midAccum a h0 [(-1 : ℤ)] + HexWalk.halfStep (hexInfra_headAccum h0 [(-1 : ℤ)]) = (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) + HexWalk.halfStep ((hexStrip_singleRight_straightSide a h0 inReg hclass).H) := by
-- proof
  apply StatMech.Universality.hexStrip_singleRight_side_exit_fires a h0 inReg hclass hstay


-- created on 2026-10-23
