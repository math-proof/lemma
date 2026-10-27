import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part4
open StatMech StatMech.FrontierA


/--
[kwGraphTransition_phaseGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwGraphTransition_phaseGauge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {phase : G.Dart → G.Dart → ℂ}
  {gauge : G.Dart → ℂ} :
-- imply
  kwGraphTransition G weight (kwPhaseGauge gauge phase) = kwGaugeConjugate gauge (kwGraphTransition G weight phase) := by
-- proof
  apply StatMech.FrontierA.kwGraphTransition_phaseGauge G weight phase gauge

/--
[kwGraphLoopScalar_phaseGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwGraphLoopScalar_phaseGauge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {gauge : G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
-- given
  (hgauge : ∀ dart, gauge dart ≠ 0) :
-- imply
  kwGraphLoopScalar G (kwPhaseGauge gauge phase) loop = kwGraphLoopScalar G phase loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopScalar_phaseGauge G phase gauge hgauge loop

/--
[kwGraphFormalLog_phaseGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwGraphFormalLog_phaseGauge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {gauge : G.Dart → ℂ}
-- given
  (hgauge : ∀ dart, gauge dart ≠ 0) :
-- imply
  kwGraphFormalLog G (kwPhaseGauge gauge phase) = kwGraphFormalLog G phase := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLog_phaseGauge G phase gauge hgauge

/--
[kwGraphFormalRoot_phaseGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwGraphFormalRoot_phaseGauge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {gauge : G.Dart → ℂ}
-- given
  (hgauge : ∀ dart, gauge dart ≠ 0) :
-- imply
  kwGraphFormalRoot G (kwPhaseGauge gauge phase) = kwGraphFormalRoot G phase := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_phaseGauge G phase gauge hgauge

/--
[kw_detWalkRoot_phaseGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kw_detWalkRoot_phaseGauge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {phase : G.Dart → G.Dart → ℂ}
  {gauge : G.Dart → ℂ}
-- given
  (hgauge : ∀ dart, gauge dart ≠ 0) :
-- imply
  ons_detWalkRoot (kwGraphTransition G weight (kwPhaseGauge gauge phase)) = ons_detWalkRoot (kwGraphTransition G weight phase) := by
-- proof
  apply StatMech.FrontierA.kw_detWalkRoot_phaseGauge G weight phase gauge hgauge

/--
[kw_det_one_sub_phaseGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kw_det_one_sub_phaseGauge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {phase : G.Dart → G.Dart → ℂ}
  {gauge : G.Dart → ℂ}
-- given
  (hgauge : ∀ dart, gauge dart ≠ 0) :
-- imply
  (1 - kwGraphTransition G weight (kwPhaseGauge gauge phase)).det = (1 - kwGraphTransition G weight phase).det := by
-- proof
  apply StatMech.FrontierA.kw_det_one_sub_phaseGauge G weight phase gauge hgauge

/--
[kwRealHalfAngleRoot_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwRealHalfAngleRoot_ne_zero_eq
  {angle : D → ℝ}
  {dart : D} :
-- imply
  kwRealHalfAngleRoot angle dart ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwRealHalfAngleRoot_ne_zero angle dart

/--
[kwPrincipalHalfAngleRoot_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwPrincipalHalfAngleRoot_ne_zero_eq
  {angle : D → Real.Angle}
  {dart : D} :
-- imply
  kwPrincipalHalfAngleRoot angle dart ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwPrincipalHalfAngleRoot_ne_zero angle dart

/--
[kwPrincipalHalfAngleRoot_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwPrincipalHalfAngleRoot_sq_eq
  {angle : D → Real.Angle}
  {dart : D} :
-- imply
  kwPrincipalHalfAngleRoot angle dart ^ 2 = Complex.exp (((angle dart).toReal : ℂ) * Complex.I) := by
-- proof
  apply StatMech.FrontierA.kwPrincipalHalfAngleRoot_sq angle dart

/--
[kwPrincipalHalfAnglePhase_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwPrincipalHalfAnglePhase_sq_eq
  {angle : D → Real.Angle}
  {dart next : D} :
-- imply
  kwPrincipalHalfAnglePhase angle dart next ^ 2 = Complex.exp (((angle next - angle dart).toReal : ℂ) * Complex.I) := by
-- proof
  apply StatMech.FrontierA.kwPrincipalHalfAnglePhase_sq angle dart next

/--
[kwPrincipalHalfAngleBranch_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwPrincipalHalfAngleBranch_sq_eq
  {angle : D → Real.Angle}
  {dart next : D} :
-- imply
  kwPrincipalHalfAngleBranch angle dart next ^ 2 = 1 := by
-- proof
  apply StatMech.FrontierA.kwPrincipalHalfAngleBranch_sq angle dart next

/--
[kwPrincipalHalfAngleBranch_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwPrincipalHalfAngleBranch_eq_one_or_neg_one_eq
  {angle : D → Real.Angle}
  {dart next : D} :
-- imply
  kwPrincipalHalfAngleBranch angle dart next = 1 ∨ kwPrincipalHalfAngleBranch angle dart next = -1 := by
-- proof
  apply StatMech.FrontierA.kwPrincipalHalfAngleBranch_eq_one_or_neg_one angle dart next

/--
[kwPrincipalHalfAnglePhase_eq_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwPrincipalHalfAnglePhase_eq_branch_eq
  {angle : D → Real.Angle} :
-- imply
  kwPrincipalHalfAnglePhase angle = kwBranchHalfAnglePhase (kwPrincipalHalfAngleRoot angle) (kwPrincipalHalfAngleBranch angle) := by
-- proof
  apply StatMech.FrontierA.kwPrincipalHalfAnglePhase_eq_branch angle

/--
[kwBranchHalfAnglePhase_eq_phaseGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwBranchHalfAnglePhase_eq_phaseGauge_eq
  {root₀ root₁ : D → ℂ}
  {branch : D → D → ℂ}
-- given
  (hroot₀ : ∀ dart, root₀ dart ≠ 0)
  (hroot₁ : ∀ dart, root₁ dart ≠ 0) :
-- imply
  kwBranchHalfAnglePhase root₁ branch = kwPhaseGauge (fun dart ↦ (root₀ dart)⁻¹ * root₁ dart) (kwBranchHalfAnglePhase root₀ branch) := by
-- proof
  apply StatMech.FrontierA.kwBranchHalfAnglePhase_eq_phaseGauge root₀ root₁ branch hroot₀ hroot₁

/--
[kwGraphFormalRoot_fixedBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwGraphFormalRoot_fixedBranch_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {root₀ root₁ : G.Dart → ℂ}
  {branch : G.Dart → G.Dart → ℂ}
-- given
  (hroot₀ : ∀ dart, root₀ dart ≠ 0)
  (hroot₁ : ∀ dart, root₁ dart ≠ 0) :
-- imply
  kwGraphFormalRoot G (kwBranchHalfAnglePhase root₁ branch) = kwGraphFormalRoot G (kwBranchHalfAnglePhase root₀ branch) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_fixedBranch G root₀ root₁ branch hroot₀ hroot₁

/--
[kwGraphFormalRoot_fixedBranch_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwGraphFormalRoot_fixedBranch_family_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {root : T → G.Dart → ℂ}
  {branch : G.Dart → G.Dart → ℂ}
  {s t : T}
-- given
  (hroot : ∀ t dart, root t dart ≠ 0) :
-- imply
  kwGraphFormalRoot G (kwBranchHalfAnglePhase (root t) branch) = kwGraphFormalRoot G (kwBranchHalfAnglePhase (root s) branch) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_fixedBranch_family G root branch hroot s t

/--
[kwGraphFormalRoot_realAngle_fixedBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwGraphFormalRoot_realAngle_fixedBranch_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {angle₀ angle₁ : G.Dart → ℝ}
  {branch : G.Dart → G.Dart → ℂ} :
-- imply
  kwGraphFormalRoot G (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₁) branch) = kwGraphFormalRoot G (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₀) branch) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_realAngle_fixedBranch G angle₀ angle₁ branch

/--
[kw_det_one_sub_realAngle_fixedBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kw_det_one_sub_realAngle_fixedBranch_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {angle₀ angle₁ : G.Dart → ℝ}
  {branch : G.Dart → G.Dart → ℂ} :
-- imply
  (1 - kwGraphTransition G weight (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₁) branch)).det = (1 - kwGraphTransition G weight (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₀) branch)).det := by
-- proof
  apply StatMech.FrontierA.kw_det_one_sub_realAngle_fixedBranch G weight angle₀ angle₁ branch

/--
[kwGraphFormalRoot_principalAngle_sameBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kwGraphFormalRoot_principalAngle_sameBranch_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {angle₀ angle₁ : G.Dart → Real.Angle}
-- given
  (hbranch : kwPrincipalHalfAngleBranch angle₁ = kwPrincipalHalfAngleBranch angle₀) :
-- imply
  kwGraphFormalRoot G (kwPrincipalHalfAnglePhase angle₁) = kwGraphFormalRoot G (kwPrincipalHalfAnglePhase angle₀) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_principalAngle_sameBranch G angle₀ angle₁ hbranch

/--
[kw_det_one_sub_principalAngle_sameBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kw_det_one_sub_principalAngle_sameBranch_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {angle₀ angle₁ : G.Dart → Real.Angle}
-- given
  (hbranch : kwPrincipalHalfAngleBranch angle₁ = kwPrincipalHalfAngleBranch angle₀) :
-- imply
  (1 - kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle₁)).det = (1 - kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle₀)).det := by
-- proof
  apply StatMech.FrontierA.kw_det_one_sub_principalAngle_sameBranch G weight angle₀ angle₁ hbranch

/--
[kw_rectilinearGraph_gaugedFormalRoot_coeff_eq_zero_of_repeated_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean)
-/
@[path]
private lemma kw_rectilinearGraph_gaugedFormalRoot_coeff_eq_zero_of_repeated_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {direction : G.Dart → Fin 4}
  {omega : ℂ}
  {gauge : G.Dart → ℂ}
  {edge : Sym2 V}
  {m : Sym2 V →₀ ℕ}
-- given
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (hgauge : ∀ dart, gauge dart ≠ 0)
  (hedge : edge ∈ G.edgeFinset)
  (hrepeated : 2 ≤ m edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G (kwPhaseGauge gauge (fun dart next ↦ ons_turnW omega (direction next) (direction dart)))) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_gaugedFormalRoot_coeff_eq_zero_of_repeated_edge G direction hdirection omega homega homega_sq gauge hgauge edge hedge m hrepeated


-- created on 2026-10-23
