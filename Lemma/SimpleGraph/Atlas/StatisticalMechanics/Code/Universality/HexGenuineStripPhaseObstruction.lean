import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexGenuineStripPhaseObstruction
open StatMech StatMech.Universality


/--
[hexGenuineStrip_obs_U](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_obs_U_eq :
-- imply
  hexGenuineStripDomain.obs (hexGenuineStripDomain.mid hexGenuineStripIncU.vtx hexGenuineStripIncU.edge) = Complex.exp (((5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I) * (hexChi : ℂ) ^ 2 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_obs_U

/--
[hexGenuineStrip_obs_Tp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_obs_Tp_eq :
-- imply
  hexGenuineStripDomain.obs (hexGenuineStripDomain.mid hexGenuineStripIncTp.vtx hexGenuineStripIncTp.edge) = Complex.exp ((-(5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I) * (hexChi : ℂ) ^ 2 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_obs_Tp

/--
[hexGenuineStrip_contourFamily_U](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_contourFamily_U_eq :
-- imply
  hexContourFamily hexGenuineStripRegion.inRegion hexGenuineStripStart 1 ({hexConcreteQ hexGenuineStripStart 1} : Set ℂ) = {[-1]} := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_contourFamily_U

/--
[hexGenuineStrip_contourFamily_Tp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_contourFamily_Tp_eq :
-- imply
  hexContourFamily hexGenuineStripRegion.inRegion hexGenuineStripStart 1 ({hexConcreteR hexGenuineStripStart 1} : Set ℂ) = {[1]} := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_contourFamily_Tp

/--
[hexGenuineStrip_contourSum_U](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_contourSum_U_eq :
-- imply
  hexContourSum hexGenuineStripRegion.inRegion hexGenuineStripStart 1 ({hexConcreteQ hexGenuineStripStart 1} : Set ℂ) hexChi = hexChi ^ 2 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_contourSum_U

/--
[hexGenuineStrip_contourSum_Tp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_contourSum_Tp_eq :
-- imply
  hexContourSum hexGenuineStripRegion.inRegion hexGenuineStripStart 1 ({hexConcreteR hexGenuineStripStart 1} : Set ℂ) hexChi = hexChi ^ 2 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_contourSum_Tp

/--
[hexGenuineStrip_core_lam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_core_lam_eq :
-- imply
  hexGenuineStripBoundaryCore.lam = 0 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_core_lam

/--
[hexGenuineStrip_core_tau](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_core_tau_eq :
-- imply
  hexGenuineStripBoundaryCore.tau = hexChi ^ 2 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_core_tau

/--
[hexGenuineStrip_core_ups](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_core_ups_eq :
-- imply
  hexGenuineStripBoundaryCore.ups = hexChi ^ 2 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_core_ups

/--
[hexGenuineStrip_fsum_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_fsum_L_eq :
-- imply
  (∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 1), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = 0 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_fsum_L

/--
[hexGenuineStrip_fsum_Tm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_fsum_Tm_eq :
-- imply
  (∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 3), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = 0 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_fsum_Tm

/--
[hexGenuineStrip_phaseL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_phaseL_eq :
-- imply
  (∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 1), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I) * ((hexBdryCl * hexGenuineStripBoundaryCore.lam : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_phaseL

/--
[hexGenuineStrip_phaseTm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_phaseTm_eq :
-- imply
  (∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 3), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I) * ((hexBdryCt * (0 : ℝ) : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_phaseTm

/--
[hexGenuineStrip_actual_phase_U](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_actual_phase_U_eq :
-- imply
  (∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 4), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = Complex.exp (((5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I) * (hexGenuineStripBoundaryCore.ups : ℂ) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_actual_phase_U

/--
[hexGenuineStrip_actual_phase_Tp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_actual_phase_Tp_eq :
-- imply
  (∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 2), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = Complex.exp ((-(5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I) * (hexGenuineStripBoundaryCore.tau : ℂ) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_actual_phase_Tp

/--
[hexGenuineStrip_ct_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_ct_lt_one_eq :
-- imply
  hexBdryCt < 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_ct_lt_one

/--
[hexGenuineStrip_corrected_phase_Tp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_corrected_phase_Tp_eq :
-- imply
  (∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 2), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = Complex.exp ((hexPhase_sideTilt (2 : ℤ) : ℝ) * Complex.I) * (Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) * (hexGenuineStripBoundaryCore.tau : ℂ)) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_corrected_phase_Tp

/--
[hexGenuineStrip_corrected_phase_U](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_corrected_phase_U_eq :
-- imply
  (∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 4), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I) * (Complex.exp ((-(Real.pi / 8 : ℝ) : ℂ) * Complex.I) * (hexGenuineStripBoundaryCore.ups : ℂ)) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_corrected_phase_U

/--
[hexUnitPhase_proj_complex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexUnitPhase_proj_complex_eq
  {cmag fSum : ℂ}
-- given
  (h : ℤ)
  (hphase : fSum = Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * cmag) :
-- imply
  hexUnit h * fSum = Complex.I * cmag := by
-- proof
  apply StatMech.Universality.hexUnitPhase_proj_complex h cmag fSum hphase

/--
[hexGenuineStrip_corrected_proj_Tp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_corrected_proj_Tp_eq :
-- imply
  hexUnit 2 * (∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 2), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = Complex.I * (Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) * (hexGenuineStripBoundaryCore.tau : ℂ)) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_corrected_proj_Tp

/--
[hexGenuineStrip_corrected_proj_U](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_corrected_proj_U_eq :
-- imply
  hexUnit 0 * (∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 4), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = Complex.I * (Complex.exp ((-(Real.pi / 8 : ℝ) : ℂ) * Complex.I) * (hexGenuineStripBoundaryCore.ups : ℂ)) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_corrected_proj_U

/--
[hexGenuineStrip_conjugate_pair_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_conjugate_pair_weight_eq :
-- imply
  2 * Real.cos (Real.pi / 8) * hexChi ^ 2 = hexChi := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_conjugate_pair_weight

/--
[hexGenuineStrip_conjugate_phase_boundary_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_conjugate_phase_boundary_identity_eq :
-- imply
  Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) * (hexGenuineStripBoundaryCore.tau : ℂ) + Complex.exp ((-(Real.pi / 8 : ℝ) : ℂ) * Complex.I) * (hexGenuineStripBoundaryCore.ups : ℂ) = (hexChi : ℂ) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_conjugate_phase_boundary_identity

/--
[hexGenuineStrip_paired_real_normalized_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_paired_real_normalized_identity_eq :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexGenuineStripBoundaryCore.lam) + Real.cos (Real.pi / 8) * (hexChi⁻¹ * hexGenuineStripBoundaryCore.tau) + Real.cos (Real.pi / 8) * (hexChi⁻¹ * hexGenuineStripBoundaryCore.ups) = 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_paired_real_normalized_identity

/--
[hexGenuineStrip_not_phaseTp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_not_phaseTp_eq :
-- imply
  ¬ ((∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 2), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = Complex.exp ((hexPhase_sideTilt (2 : ℤ) : ℝ) * Complex.I) * ((hexBdryCt * hexGenuineStripBoundaryCore.tau : ℝ) : ℂ)) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_not_phaseTp

/--
[hexGenuineStrip_not_phaseU](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_not_phaseU_eq :
-- imply
  ¬ ((∑ e ∈ (hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior).filter (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 4), hexGenuineStripDomain.obs (hexGenuineStripDomain.mid e.vtx e.edge)) = Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I) * ((hexGenuineStripBoundaryCore.ups : ℝ) : ℂ)) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_not_phaseU

/--
[hexGenuineStrip_normalized_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_normalized_value_eq :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexGenuineStripBoundaryCore.lam) + hexBdryCt * (hexChi⁻¹ * hexGenuineStripBoundaryCore.tau) + hexChi⁻¹ * hexGenuineStripBoundaryCore.ups = hexChi * (hexBdryCt + 1) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_normalized_value

/--
[hexGenuineStrip_chi_mul_ct_add_one_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_chi_mul_ct_add_one_lt_one_eq :
-- imply
  hexChi * (hexBdryCt + 1) < 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_chi_mul_ct_add_one_lt_one

/--
[hexGenuineStrip_normalized_value_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_normalized_value_lt_one_eq :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexGenuineStripBoundaryCore.lam) + hexBdryCt * (hexChi⁻¹ * hexGenuineStripBoundaryCore.tau) + hexChi⁻¹ * hexGenuineStripBoundaryCore.ups < 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_normalized_value_lt_one

/--
[hexGenuineStrip_normalized_value_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_normalized_value_ne_one_eq :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexGenuineStripBoundaryCore.lam) + hexBdryCt * (hexChi⁻¹ * hexGenuineStripBoundaryCore.tau) + hexChi⁻¹ * hexGenuineStripBoundaryCore.ups ≠ 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_normalized_value_ne_one

/--
[hexGenuineStrip_noFourPhaseData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_noFourPhaseData_eq
  {G : HexRegion} :
-- imply
  ¬ Nonempty (HexFiniteStripFourPhaseData hexGenuineStripBoundaryCore G) := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_noFourPhaseData G

/--
[hexGenuineStrip_paired_real_normalized_contour_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_paired_real_normalized_contour_identity_eq :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi) + Real.cos (Real.pi / 8) * (hexChi⁻¹ * (hexContourTauPlus hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi + hexContourTauMinus hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi)) + Real.cos (Real.pi / 8) * (hexChi⁻¹ * hexContourUpsilon hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi) = 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_paired_real_normalized_contour_identity

/--
[hexGenuineStrip_normalized_contour_value_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_normalized_contour_value_lt_one_eq :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi + hexContourTauMinus hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi)) + hexChi⁻¹ * hexContourUpsilon hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi < 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_normalized_contour_value_lt_one

/--
[hexGenuineStrip_normalized_contour_value_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripPhaseObstruction.lean)
-/
@[path]
private lemma hexGenuineStrip_normalized_contour_value_ne_one_eq :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi + hexContourTauMinus hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi)) + hexChi⁻¹ * hexContourUpsilon hexGenuineStripRegion.inRegion hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi ≠ 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_normalized_contour_value_ne_one


-- created on 2026-10-23
