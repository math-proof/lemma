/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part5
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager


theorem kwPrincipalHalfAngleBranch_sq
    {D : Type*} (angle : D → Real.Angle) (dart next : D) :
    kwPrincipalHalfAngleBranch angle dart next ^ 2 = 1 := by
  let a : ℝ := (angle dart).toReal
  let delta : ℝ := (angle next - angle dart).toReal
  let b : ℝ := (angle next).toReal
  have hxAngle : ((a + delta - b : ℝ) : Real.Angle) = 0 := by
    dsimp only [a, delta, b]
    simp only [Real.Angle.coe_sub, Real.Angle.coe_add,
      Real.Angle.coe_toReal]
    abel
  obtain ⟨k, hk⟩ := Real.Angle.coe_eq_zero_iff.mp hxAngle
  have hexp : Complex.exp (((a + delta - b : ℝ) : ℂ) * Complex.I) = 1 := by
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨k, ?_⟩
    rw [← hk]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  unfold kwPrincipalHalfAngleBranch
  rw [pow_two]
  calc
    (kwPrincipalHalfAngleRoot angle dart *
          kwPrincipalHalfAnglePhase angle dart next *
          (kwPrincipalHalfAngleRoot angle next)⁻¹) *
        (kwPrincipalHalfAngleRoot angle dart *
          kwPrincipalHalfAnglePhase angle dart next *
          (kwPrincipalHalfAngleRoot angle next)⁻¹) =
      kwPrincipalHalfAngleRoot angle dart ^ 2 *
        kwPrincipalHalfAnglePhase angle dart next ^ 2 *
        (kwPrincipalHalfAngleRoot angle next ^ 2)⁻¹ := by ring
    _ = Complex.exp ((a : ℂ) * Complex.I) *
        Complex.exp ((delta : ℂ) * Complex.I) *
        (Complex.exp ((b : ℂ) * Complex.I))⁻¹ := by
      rw [kwPrincipalHalfAngleRoot_sq,
        kwPrincipalHalfAnglePhase_sq,
        kwPrincipalHalfAngleRoot_sq]
    _ = Complex.exp (((a + delta - b : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = 1 := hexp

theorem kwPrincipalHalfAngleBranch_eq_one_or_neg_one
    {D : Type*} (angle : D → Real.Angle) (dart next : D) :
    kwPrincipalHalfAngleBranch angle dart next = 1 ∨
      kwPrincipalHalfAngleBranch angle dart next = -1 :=
  sq_eq_one_iff.mp (kwPrincipalHalfAngleBranch_sq angle dart next)


theorem kwPrincipalHalfAnglePhase_eq_branch
    {D : Type*} (angle : D → Real.Angle) :
    kwPrincipalHalfAnglePhase angle =
      kwBranchHalfAnglePhase (kwPrincipalHalfAngleRoot angle)
        (kwPrincipalHalfAngleBranch angle) := by
  funext dart next
  simp only [kwBranchHalfAnglePhase, kwPrincipalHalfAngleBranch]
  field_simp [kwPrincipalHalfAngleRoot_ne_zero angle dart,
    kwPrincipalHalfAngleRoot_ne_zero angle next]


theorem kwBranchHalfAnglePhase_eq_phaseGauge
    {D : Type*} (root₀ root₁ : D → ℂ) (branch : D → D → ℂ)
    (hroot₀ : ∀ dart, root₀ dart ≠ 0)
    (hroot₁ : ∀ dart, root₁ dart ≠ 0) :
    kwBranchHalfAnglePhase root₁ branch =
      kwPhaseGauge (fun dart ↦ (root₀ dart)⁻¹ * root₁ dart)
        (kwBranchHalfAnglePhase root₀ branch) := by
  funext dart next
  simp only [kwBranchHalfAnglePhase, kwPhaseGauge]
  field_simp [hroot₀ dart, hroot₀ next, hroot₁ dart, hroot₁ next]


theorem kwGraphFormalRoot_fixedBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root₀ root₁ : G.Dart → ℂ) (branch : G.Dart → G.Dart → ℂ)
    (hroot₀ : ∀ dart, root₀ dart ≠ 0)
    (hroot₁ : ∀ dart, root₁ dart ≠ 0) :
    kwGraphFormalRoot G (kwBranchHalfAnglePhase root₁ branch) =
      kwGraphFormalRoot G (kwBranchHalfAnglePhase root₀ branch) := by
  rw [kwBranchHalfAnglePhase_eq_phaseGauge root₀ root₁ branch
    hroot₀ hroot₁]
  apply kwGraphFormalRoot_phaseGauge
  intro dart
  exact mul_ne_zero (inv_ne_zero (hroot₀ dart)) (hroot₁ dart)


theorem kwGraphFormalRoot_fixedBranch_family
    {V T : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : T → G.Dart → ℂ) (branch : G.Dart → G.Dart → ℂ)
    (hroot : ∀ t dart, root t dart ≠ 0) (s t : T) :
    kwGraphFormalRoot G (kwBranchHalfAnglePhase (root t) branch) =
      kwGraphFormalRoot G (kwBranchHalfAnglePhase (root s) branch) :=
  kwGraphFormalRoot_fixedBranch G (root s) (root t) branch
    (hroot s) (hroot t)


theorem kwGraphFormalRoot_realAngle_fixedBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle₀ angle₁ : G.Dart → ℝ)
    (branch : G.Dart → G.Dart → ℂ) :
    kwGraphFormalRoot G
        (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₁) branch) =
      kwGraphFormalRoot G
        (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₀) branch) :=
  kwGraphFormalRoot_fixedBranch G _ _ branch
    (kwRealHalfAngleRoot_ne_zero angle₀)
    (kwRealHalfAngleRoot_ne_zero angle₁)


theorem kw_det_one_sub_realAngle_fixedBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (angle₀ angle₁ : G.Dart → ℝ)
    (branch : G.Dart → G.Dart → ℂ) :
    (1 - kwGraphTransition G weight
        (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₁) branch)).det =
      (1 - kwGraphTransition G weight
        (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₀) branch)).det := by
  rw [kwBranchHalfAnglePhase_eq_phaseGauge
    (kwRealHalfAngleRoot angle₀) (kwRealHalfAngleRoot angle₁) branch
    (kwRealHalfAngleRoot_ne_zero angle₀)
    (kwRealHalfAngleRoot_ne_zero angle₁)]
  apply kw_det_one_sub_phaseGauge
  intro dart
  exact mul_ne_zero
    (inv_ne_zero (kwRealHalfAngleRoot_ne_zero angle₀ dart))
    (kwRealHalfAngleRoot_ne_zero angle₁ dart)


theorem kwGraphFormalRoot_principalAngle_sameBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle₀ angle₁ : G.Dart → Real.Angle)
    (hbranch : kwPrincipalHalfAngleBranch angle₁ =
      kwPrincipalHalfAngleBranch angle₀) :
    kwGraphFormalRoot G (kwPrincipalHalfAnglePhase angle₁) =
      kwGraphFormalRoot G (kwPrincipalHalfAnglePhase angle₀) := by
  rw [kwPrincipalHalfAnglePhase_eq_branch angle₁,
    kwPrincipalHalfAnglePhase_eq_branch angle₀, hbranch]
  exact kwGraphFormalRoot_fixedBranch G _ _ _
    (kwPrincipalHalfAngleRoot_ne_zero angle₀)
    (kwPrincipalHalfAngleRoot_ne_zero angle₁)


theorem kw_det_one_sub_principalAngle_sameBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (angle₀ angle₁ : G.Dart → Real.Angle)
    (hbranch : kwPrincipalHalfAngleBranch angle₁ =
      kwPrincipalHalfAngleBranch angle₀) :
    (1 - kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase angle₁)).det =
      (1 - kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase angle₀)).det := by
  rw [kwPrincipalHalfAnglePhase_eq_branch angle₁,
    kwPrincipalHalfAnglePhase_eq_branch angle₀, hbranch]
  rw [kwBranchHalfAnglePhase_eq_phaseGauge
    (kwPrincipalHalfAngleRoot angle₀)
    (kwPrincipalHalfAngleRoot angle₁)
    (kwPrincipalHalfAngleBranch angle₀)
    (kwPrincipalHalfAngleRoot_ne_zero angle₀)
    (kwPrincipalHalfAngleRoot_ne_zero angle₁)]
  apply kw_det_one_sub_phaseGauge
  intro dart
  exact mul_ne_zero
    (inv_ne_zero (kwPrincipalHalfAngleRoot_ne_zero angle₀ dart))
    (kwPrincipalHalfAngleRoot_ne_zero angle₁ dart)


theorem kw_rectilinearGraph_gaugedFormalRoot_coeff_eq_zero_of_repeated_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (direction : G.Dart → Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (gauge : G.Dart → ℂ) (hgauge : ∀ dart, gauge dart ≠ 0)
    (edge : Sym2 V) (hedge : edge ∈ G.edgeFinset)
    (m : Sym2 V →₀ ℕ) (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G
        (kwPhaseGauge gauge (fun dart next ↦
          ons_turnW omega (direction next) (direction dart)))) = 0 := by
  rw [kwGraphFormalRoot_phaseGauge G _ gauge hgauge]
  exact kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated_edge
    G direction hdirection omega homega homega_sq edge hedge m hrepeated

end StatMech.FrontierA
