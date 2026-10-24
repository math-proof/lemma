import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexSingleStartPhaseRepair
open StatMech StatMech.Universality StatMech.Universality.HexSingleStartPhaseData StatMech.Universality.HexFiniteStripBoundaryData


/--
[startFiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma startFiber_card_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  ((D.incidences \ P.interior).filter (fun e ↦ hexRegionClsInc R D e = 0)).card = 1 := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.startFiber_card

/--
[eq_startInc_of_mem_startFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma eq_startInc_of_mem_startFiber_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
  {e : HexIncidence V}
-- given
  (he : e ∈ (D.incidences \ P.interior).filter (fun e ↦ hexRegionClsInc R D e = 0)) :
-- imply
  e = H.startInc := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.eq_startInc_of_mem_startFiber e he

/--
[heading_eq_four_on_startFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma heading_eq_four_on_startFiber_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
  {e : HexIncidence V}
-- given
  (he : e ∈ (D.incidences \ P.interior).filter (fun e ↦ hexRegionClsInc R D e = 0)) :
-- imply
  H.heading e.vtx e.edge = 4 := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.heading_eq_four_on_startFiber e he

/--
[startProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma startProjection_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  ((1 / 2 : ℂ) * hexUnit 4) * (∑ e ∈ (D.incidences \ P.interior).filter (fun e ↦ hexRegionClsInc R D e = 0), D.obs (D.mid e.vtx e.edge)) = Complex.I * (((-1 : ℝ) * (H.Fa / 2) : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.startProjection

/--
[startProjection_hexChi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma startProjection_hexChi_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
-- given
  (hFa : H.Fa = hexChi) :
-- imply
  ((1 / 2 : ℂ) * hexUnit 4) * (∑ e ∈ (D.incidences \ P.interior).filter (fun e ↦ hexRegionClsInc R D e = 0), D.obs (D.mid e.vtx e.edge)) = Complex.I * (((-1 : ℝ) * (hexChi / 2) : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.startProjection_hexChi hFa

/--
[toHalfStartRegionAssign_lam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma toHalfStartRegionAssign_lam_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  H.toHalfStartRegionAssign.lam = H.lam := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.toHalfStartRegionAssign_lam

/--
[toHalfStartRegionAssign_taup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma toHalfStartRegionAssign_taup_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  H.toHalfStartRegionAssign.taup = H.taup := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.toHalfStartRegionAssign_taup

/--
[toHalfStartRegionAssign_taum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma toHalfStartRegionAssign_taum_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  H.toHalfStartRegionAssign.taum = H.taum := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.toHalfStartRegionAssign_taum

/--
[toHalfStartRegionAssign_ups](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma toHalfStartRegionAssign_ups_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  H.toHalfStartRegionAssign.ups = H.ups := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.toHalfStartRegionAssign_ups

/--
[toHalfStartRegionAssign_Fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma toHalfStartRegionAssign_Fa_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  H.toHalfStartRegionAssign.Fa = H.Fa / 2 := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.toHalfStartRegionAssign_Fa

/--
[hexBdryAssign_identity_fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma hexBdryAssign_identity_fa_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
  {A : HexRegionAssign D P R}
-- given
  (hsub : P.interior ⊆ D.incidences) :
-- imply
  hexBdryCl * A.lam + hexBdryCt * (A.taup + A.taum) + A.ups = A.Fa := by
-- proof
  apply StatMech.Universality.hexBdryAssign_identity_fa hsub A

/--
[correctedInterface_identity_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma correctedInterface_identity_half_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
-- given
  (hsub : P.interior ⊆ D.incidences) :
-- imply
  hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups = H.Fa / 2 := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.correctedInterface_identity_half hsub

/--
[correctedInterface_identity_hexChi_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma correctedInterface_identity_hexChi_half_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
-- given
  (hsub : P.interior ⊆ D.incidences)
  (hFa : H.Fa = hexChi) :
-- imply
  hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups = hexChi / 2 := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.correctedInterface_identity_hexChi_half hsub hFa

/--
[correctedInterface_normalized_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma correctedInterface_normalized_identity_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
-- given
  (hsub : P.interior ⊆ D.incidences)
  (hFa : H.Fa = hexChi) :
-- imply
  hexBdryCl * ((2 * hexChi⁻¹) * H.lam) + hexBdryCt * ((2 * hexChi⁻¹) * (H.taup + H.taum)) + (2 * hexChi⁻¹) * H.ups = 1 := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.correctedInterface_normalized_identity hsub hFa

/--
[Fa_eq_boundaryData_Fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma Fa_eq_boundaryData_Fa_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
  {Rf : HexFiniteRegion}
  {h0 : ℤ}
  {B : HexFiniteStripBoundaryData Rf h0 D P}
-- given
  (hstart : R.start = Rf.start) :
-- imply
  H.Fa = B.Fa := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.Fa_eq_boundaryData_Fa B hstart

/--
[Fa_eq_hexChi_of_boundaryData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma Fa_eq_hexChi_of_boundaryData_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
  {Rf : HexFiniteRegion}
  {h0 : ℤ}
  {B : HexFiniteStripBoundaryData Rf h0 D P}
-- given
  (hstart : R.start = Rf.start) :
-- imply
  H.Fa = hexChi := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.Fa_eq_hexChi_of_boundaryData B hstart

/--
[diagnostic_half_identity_of_boundaryData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma diagnostic_half_identity_of_boundaryData_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
  {Rf : HexFiniteRegion}
  {h0 : ℤ}
  {B : HexFiniteStripBoundaryData Rf h0 D P}
-- given
  (hstart : R.start = Rf.start) :
-- imply
  hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups = hexChi / 2 := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.diagnostic_half_identity_of_boundaryData B hstart

/--
[boundaryData_identity_of_halfScaled_contours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma boundaryData_identity_of_halfScaled_contours_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
  {Rf : HexFiniteRegion}
  {h0 : ℤ}
  {B : HexFiniteStripBoundaryData Rf h0 D P}
-- given
  (hstart : R.start = Rf.start)
  (hlam : H.lam = B.lam / 2)
  (htau : H.taup + H.taum = B.tau / 2)
  (hups : H.ups = B.ups / 2) :
-- imply
  hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = hexChi := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.boundaryData_identity_of_halfScaled_contours B hstart hlam htau hups

/--
[normalized_boundaryData_identity_of_halfScaled_contours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma normalized_boundaryData_identity_of_halfScaled_contours_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
  {Rf : HexFiniteRegion}
  {h0 : ℤ}
  {B : HexFiniteStripBoundaryData Rf h0 D P}
-- given
  (hstart : R.start = Rf.start)
  (hlam : H.lam = B.lam / 2)
  (htau : H.taup + H.taum = B.tau / 2)
  (hups : H.ups = B.ups / 2) :
-- imply
  hexBdryCl * (hexChi⁻¹ * B.lam) + hexBdryCt * (hexChi⁻¹ * B.tau) + hexChi⁻¹ * B.ups = 1 := by
-- proof
  apply StatMech.Universality.HexSingleStartPhaseData.normalized_boundaryData_identity_of_halfScaled_contours B hstart hlam htau hups

/--
[obs_start_eq_hexChi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean)
-/
@[path]
private lemma obs_start_eq_hexChi_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexFiniteStripBoundaryData R h0 D P} :
-- imply
  D.obs R.start = (hexChi : ℂ) := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.obs_start_eq_hexChi B


-- created on 2026-10-23
