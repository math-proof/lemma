import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexStartPhaseRepair
open StatMech StatMech.Universality StatMech.Universality.HexFiniteStripBoundaryCore StatMech.Universality.HexFiniteStripFourPhaseData


/--
[HexFiniteStripIncidenceEnumeration.exists_startIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma exists_startIncidence_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexFiniteStripBoundaryData R h0 D P}
  {E : HexFiniteStripIncidenceEnumeration B} :
-- imply
  ∃ eA : HexIncidence V, hexFiniteStripPhysicalStartFiber (R := R) P = {eA} := by
-- proof
  apply StatMech.Universality.HexFiniteStripIncidenceEnumeration.exists_startIncidence E

/--
[HexFiniteStripIncidenceEnumeration.startFiber_card_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma startFiber_card_eq_one_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexFiniteStripBoundaryData R h0 D P}
  {E : HexFiniteStripIncidenceEnumeration B} :
-- imply
  (hexFiniteStripPhysicalStartFiber (R := R) P).card = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripIncidenceEnumeration.startFiber_card_eq_one E

/--
[HexFiniteStripIncidenceEnumeration.exists_classifiedStartIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma exists_classifiedStartIncidence_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexFiniteStripBoundaryData R h0 D P}
  {E : HexFiniteStripIncidenceEnumeration B}
  {G : HexRegion}
-- given
  (hclass : ∀ e ∈ D.incidences \ P.interior, hexRegionClsInc G D e = 0 ↔ D.mid e.vtx e.edge = R.start) :
-- imply
  ∃ eA : HexIncidence V, (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0) = {eA} := by
-- proof
  apply StatMech.Universality.HexFiniteStripIncidenceEnumeration.exists_classifiedStartIncidence E G hclass

/--
[HexFiniteStripIncidenceEnumeration.exists_classifiedStartData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma exists_classifiedStartData_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexFiniteStripBoundaryData R h0 D P}
  {E : HexFiniteStripIncidenceEnumeration B}
  {G : HexRegion}
-- given
  (hstart : G.start = R.start)
  (hclass : ∀ e ∈ D.incidences \ P.interior, hexRegionClsInc G D e = 0 ↔ D.mid e.vtx e.edge = R.start) :
-- imply
  ∃ eA : HexIncidence V, (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0) = {eA} ∧ D.mid eA.vtx eA.edge = G.start := by
-- proof
  apply StatMech.Universality.HexFiniteStripIncidenceEnumeration.exists_classifiedStartData E G hstart hclass

/--
[hexStart_hexUnit_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma hexStart_hexUnit_four_eq
  [DecidableEq V] :
-- imply
  hexUnit (4 : ℤ) = -Complex.I := by
-- proof
  apply StatMech.Universality.hexStart_hexUnit_four

/--
[hexUnitPhase_proj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma hexUnitPhase_proj_eq
  [DecidableEq V]
  {cmag : ℝ}
  {fSum : ℂ}
-- given
  (h : ℤ)
  (hphase : fSum = Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ)) :
-- imply
  hexUnit h * fSum = Complex.I * (cmag : ℂ) := by
-- proof
  apply StatMech.Universality.hexUnitPhase_proj h cmag fSum hphase

/--
[hexUnitPhase_half_proj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma hexUnitPhase_half_proj_eq
  [DecidableEq V]
  {coeff value : ℝ}
  {fSum : ℂ}
-- given
  (h : ℤ)
  (hphase : fSum = Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * ((coeff * value : ℝ) : ℂ)) :
-- imply
  ((1 / 2 : ℂ) * hexUnit h) * fSum = Complex.I * ((coeff * (value / 2) : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexUnitPhase_half_proj h coeff value fSum hphase

/--
[Fa_eq_hexChi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma Fa_eq_hexChi_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {C : HexFiniteStripBoundaryCore R h0 D P} :
-- imply
  C.Fa = hexChi := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryCore.Fa_eq_hexChi C

/--
[ofBoundaryData_Fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma ofBoundaryData_Fa_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {B : HexFiniteStripBoundaryData R h0 D P} :
-- imply
  (ofBoundaryData B).Fa = B.Fa := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryCore.ofBoundaryData_Fa B

/--
[startFSum_eq_Fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma startFSum_eq_Fa_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0), D.obs (D.mid e.vtx e.edge)) = (C.Fa : ℂ) := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.startFSum_eq_Fa

/--
[startFSum_eq_hexChi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma startFSum_eq_hexChi_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0), D.obs (D.mid e.vtx e.edge)) = (hexChi : ℂ) := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.startFSum_eq_hexChi

/--
[normalized_startFSum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma normalized_startFSum_eq_one_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  (hexChi : ℂ)⁻¹ * (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0), D.obs (D.mid e.vtx e.edge)) = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.normalized_startFSum_eq_one

/--
[projA_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma projA_unit_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  hexUnit 4 * (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0), D.obs (D.mid e.vtx e.edge)) = Complex.I * (((-1 : ℝ) * C.Fa : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.projA_unit

/--
[normalized_startContribution_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma normalized_startContribution_eq_neg_one_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  -(hexChi : ℂ)⁻¹ * (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0), D.obs (D.mid e.vtx e.edge)) = -1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.normalized_startContribution_eq_neg_one

/--
[hHeadA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma hHeadA_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0), H.heading e.vtx e.edge = 4 := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.hHeadA

/--
[toHalfRegionAssign_lam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma toHalfRegionAssign_lam_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  H.toHalfRegionAssign.lam = C.lam / 2 := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.toHalfRegionAssign_lam

/--
[toHalfRegionAssign_taup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma toHalfRegionAssign_taup_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  H.toHalfRegionAssign.taup = H.taup / 2 := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.toHalfRegionAssign_taup

/--
[toHalfRegionAssign_taum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma toHalfRegionAssign_taum_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  H.toHalfRegionAssign.taum = H.taum / 2 := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.toHalfRegionAssign_taum

/--
[toHalfRegionAssign_ups](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma toHalfRegionAssign_ups_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  H.toHalfRegionAssign.ups = C.ups / 2 := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.toHalfRegionAssign_ups

/--
[toHalfRegionAssign_Fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma toHalfRegionAssign_Fa_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  H.toHalfRegionAssign.Fa = C.Fa / 2 := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.toHalfRegionAssign_Fa

/--
[boundary_identity_fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma boundary_identity_fa_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  hexBdryCl * C.lam + hexBdryCt * (H.taup + H.taum) + C.ups = C.Fa := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.boundary_identity_fa

/--
[normalized_boundary_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma normalized_boundary_identity_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  hexBdryCl * (hexChi⁻¹ * C.lam) + hexBdryCt * (hexChi⁻¹ * C.tau) + hexChi⁻¹ * C.ups = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.normalized_boundary_identity

/--
[normalized_contour_boundary_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean)
-/
@[path]
private lemma normalized_contour_boundary_identity_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 C.sides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus R.inRegion R.start h0 C.sides hexChi + hexContourTauMinus R.inRegion R.start h0 C.sides hexChi)) + hexChi⁻¹ * hexContourUpsilon R.inRegion R.start h0 C.sides hexChi = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripFourPhaseData.normalized_contour_boundary_identity


-- created on 2026-10-23
