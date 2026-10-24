import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexBoundaryPhases
open StatMech StatMech.Universality StatMech.Universality.HexPhaseData


/--
[hexPhase_sideTilt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_sideTilt_one_eq :
-- imply
  hexPhase_sideTilt 1 = 0 := by
-- proof
  apply StatMech.Universality.hexPhase_sideTilt_one

/--
[hexPhase_keyfac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_keyfac_eq
  {θ : ℝ} :
-- imply
  Complex.I * Complex.exp ((-θ : ℝ) * Complex.I) = Complex.exp (((Real.pi / 2 - θ : ℝ) : ℂ) * Complex.I) := by
-- proof
  apply StatMech.Universality.hexPhase_keyfac θ

/--
[hexPhase_hexUnit_normalForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_hexUnit_normalForm_eq
-- given
  (h : ℤ) :
-- imply
  hexUnit h = Complex.I * Complex.exp ((-(hexPhase_sideTilt h) : ℝ) * Complex.I) := by
-- proof
  apply StatMech.Universality.hexPhase_hexUnit_normalForm h

/--
[hexPhase_reflection_madeReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_reflection_madeReal_eq
  {φ r : ℝ} :
-- imply
  Complex.exp ((-φ : ℝ) * Complex.I) * (r : ℂ) + Complex.exp ((φ : ℝ) * Complex.I) * (r : ℂ) = ((2 * Real.cos φ * r : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexPhase_reflection_madeReal φ r

/--
[hexPhase_cl_from_turning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_cl_from_turning_eq :
-- imply
  hexBdryCl = -Real.cos (5 * Real.pi / 8) := by
-- proof
  apply StatMech.Universality.hexPhase_cl_from_turning

/--
[hexPhase_cl_winding_angle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_cl_winding_angle_eq :
-- imply
  (5 * Real.pi / 8 : ℝ) = (5 / 8 : ℝ) * Real.pi := by
-- proof
  apply StatMech.Universality.hexPhase_cl_winding_angle

/--
[hexPhase_ct_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_ct_eq_eq :
-- imply
  hexBdryCt = Real.cos (Real.pi / 4) := by
-- proof
  apply StatMech.Universality.hexPhase_ct_eq

/--
[hexPhase_cu_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_cu_eq_eq :
-- imply
  (1 : ℝ) = Real.cos 0 := by
-- proof
  apply StatMech.Universality.hexPhase_cu_eq

/--
[hexPhase_proj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_proj_eq
  {cmag : ℝ}
  {fSum : ℂ}
-- given
  (h : ℤ)
  (hphase : fSum = 2 * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ)) :
-- imply
  ((1 / 2 : ℂ) * hexUnit h) * fSum = Complex.I * (cmag : ℂ) := by
-- proof
  apply StatMech.Universality.hexPhase_proj h cmag fSum hphase

/--
[hexPhase_proj_atTilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_proj_atTilt_eq
  {θ : ℝ}
  {c : ℂ} :
-- imply
  (Complex.I * Complex.exp ((-θ : ℝ) * Complex.I)) * (Complex.exp ((θ : ℝ) * Complex.I) * ((Real.cos θ : ℂ) * c)) = Complex.I * ((Real.cos θ : ℂ) * c) := by
-- proof
  apply StatMech.Universality.hexPhase_proj_atTilt θ c

/--
[hexPhase_projA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_projA_eq
  [DecidableEq V]
  {Fa : ℝ}
-- given
  (headA : ℤ)
  (hphase : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 0), D.obs (D.mid e.vtx e.edge)) = 2 * Complex.exp ((hexPhase_sideTilt headA : ℝ) * Complex.I) * (((-1 : ℝ) * Fa : ℝ) : ℂ)) :
-- imply
  ((1 / 2 : ℂ) * hexUnit headA) * (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 0), D.obs (D.mid e.vtx e.edge)) = Complex.I * (((-1 : ℝ) * Fa : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexPhase_projA headA Fa hphase

/--
[hexPhase_projL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_projL_eq
  [DecidableEq V]
  {lam : ℝ}
-- given
  (headL : ℤ)
  (hphase : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 1), D.obs (D.mid e.vtx e.edge)) = 2 * Complex.exp ((hexPhase_sideTilt headL : ℝ) * Complex.I) * ((hexBdryCl * lam : ℝ) : ℂ)) :
-- imply
  ((1 / 2 : ℂ) * hexUnit headL) * (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 1), D.obs (D.mid e.vtx e.edge)) = Complex.I * ((hexBdryCl * lam : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexPhase_projL headL lam hphase

/--
[hexPhase_projTp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_projTp_eq
  [DecidableEq V]
  {taup : ℝ}
-- given
  (headTp : ℤ)
  (hphase : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 2), D.obs (D.mid e.vtx e.edge)) = 2 * Complex.exp ((hexPhase_sideTilt headTp : ℝ) * Complex.I) * ((hexBdryCt * taup : ℝ) : ℂ)) :
-- imply
  ((1 / 2 : ℂ) * hexUnit headTp) * (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 2), D.obs (D.mid e.vtx e.edge)) = Complex.I * ((hexBdryCt * taup : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexPhase_projTp headTp taup hphase

/--
[hexPhase_projTm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_projTm_eq
  [DecidableEq V]
  {taum : ℝ}
-- given
  (headTm : ℤ)
  (hphase : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 3), D.obs (D.mid e.vtx e.edge)) = 2 * Complex.exp ((hexPhase_sideTilt headTm : ℝ) * Complex.I) * ((hexBdryCt * taum : ℝ) : ℂ)) :
-- imply
  ((1 / 2 : ℂ) * hexUnit headTm) * (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 3), D.obs (D.mid e.vtx e.edge)) = Complex.I * ((hexBdryCt * taum : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexPhase_projTm headTm taum hphase

/--
[hexPhase_projU](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_projU_eq
  [DecidableEq V]
  {ups : ℝ}
-- given
  (headU : ℤ)
  (hphase : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 4), D.obs (D.mid e.vtx e.edge)) = 2 * Complex.exp ((hexPhase_sideTilt headU : ℝ) * Complex.I) * ((ups : ℝ) : ℂ)) :
-- imply
  ((1 / 2 : ℂ) * hexUnit headU) * (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 4), D.obs (D.mid e.vtx e.edge)) = Complex.I * ((ups : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexPhase_projU headU ups hphase

/--
[toRegionAssign_lam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma toRegionAssign_lam_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  H.toRegionAssign.lam = H.lam := by
-- proof
  apply StatMech.Universality.HexPhaseData.toRegionAssign_lam

/--
[toRegionAssign_taup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma toRegionAssign_taup_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  H.toRegionAssign.taup = H.taup := by
-- proof
  apply StatMech.Universality.HexPhaseData.toRegionAssign_taup

/--
[toRegionAssign_taum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma toRegionAssign_taum_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  H.toRegionAssign.taum = H.taum := by
-- proof
  apply StatMech.Universality.HexPhaseData.toRegionAssign_taum

/--
[toRegionAssign_ups](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma toRegionAssign_ups_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  H.toRegionAssign.ups = H.ups := by
-- proof
  apply StatMech.Universality.HexPhaseData.toRegionAssign_ups

/--
[toRegionAssign_Fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma toRegionAssign_Fa_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  H.toRegionAssign.Fa = H.Fa := by
-- proof
  apply StatMech.Universality.HexPhaseData.toRegionAssign_Fa

/--
[hexPhase_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_identity_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
  {H : HexPhaseData D P R}
-- given
  (hsub : P.interior ⊆ D.incidences)
  (hFa : H.Fa = 1) :
-- imply
  hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups = 1 := by
-- proof
  apply StatMech.Universality.hexPhase_identity hsub H hFa

/--
[hexPhase_identity_scales](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_identity_scales_eq
  [DecidableEq V]
  {D : ℕ → HexDomain V}
  {P : ∀ v, (D v).InteriorPairing}
  {R : ℕ → HexRegion}
-- given
  (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
  (H : ∀ v, HexPhaseData (D v) (P v) (R v))
  (hFa : ∀ v, 1 ≤ v → (H v).Fa = 1) :
-- imply
  ∀ v, 1 ≤ v → hexBdryCl * (H v).lam + hexBdryCt * ((H v).taup + (H v).taum) + (H v).ups = 1 := by
-- proof
  apply StatMech.Universality.hexPhase_identity_scales hsub H hFa

/--
[hexPhase_hexCell_normalForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_hexCell_normalForm_eq
  [DecidableEq V]
  {j : Fin 3} :
-- imply
  hexUnit (2 * (j : ℤ)) = Complex.I * Complex.exp ((-(hexPhase_sideTilt (2 * (j : ℤ))) : ℝ) * Complex.I) := by
-- proof
  apply StatMech.Universality.hexPhase_hexCell_normalForm j

/--
[hexPhase_proj_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean)
-/
@[path]
private lemma hexPhase_proj_fires_eq
  [DecidableEq V]
  {cmag : ℝ}
-- given
  (h : ℤ) :
-- imply
  ((1 / 2 : ℂ) * hexUnit h) * (2 * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ)) = Complex.I * (cmag : ℂ) := by
-- proof
  apply StatMech.Universality.hexPhase_proj_fires h cmag


-- created on 2026-10-23
