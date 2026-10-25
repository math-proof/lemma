/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part4
import Mathlib.Topology.Connected.TotallyDisconnected
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy
open scoped BigOperators
open Set SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


theorem kwLoopPhaseProduct_branchHalfAngle
    {D : Type*} {n : ℕ} [NeZero n]
    (root : D → ℂ) (branch : D → D → ℂ)
    (hroot : ∀ dart, root dart ≠ 0) (loop : Fin n → D) :
    kwLoopPhaseProduct (kwBranchHalfAnglePhase root branch) loop =
      kwLoopPhaseProduct branch loop := by
  unfold kwLoopPhaseProduct kwBranchHalfAnglePhase
  simp_rw [mul_assoc]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  have hreindex : (∏ k, root (loop (k + 1))) = ∏ k, root (loop k) :=
    Equiv.prod_comp (Equiv.addRight (1 : Fin n))
      (fun k ↦ root (loop k))
  rw [hreindex]
  have hprod : (∏ k, root (loop k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ ↦ hroot (loop k))
  calc
    (∏ k, root (loop k))⁻¹ *
        ((∏ k, branch (loop k) (loop (k + 1))) *
          ∏ k, root (loop k)) =
      ((∏ k, root (loop k))⁻¹ * ∏ k, root (loop k)) *
        ∏ k, branch (loop k) (loop (k + 1)) := by ring
    _ = ∏ k, branch (loop k) (loop (k + 1)) := by
      rw [inv_mul_cancel₀ hprod, one_mul]


theorem kwLoopPhaseProduct_principal_eq_branch
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D) :
    kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop =
      kwLoopPhaseProduct (kwPrincipalHalfAngleBranch angle) loop := by
  rw [kwPrincipalHalfAnglePhase_eq_branch]
  exact kwLoopPhaseProduct_branchHalfAngle
    (kwPrincipalHalfAngleRoot angle)
    (kwPrincipalHalfAngleBranch angle)
    (kwPrincipalHalfAngleRoot_ne_zero angle) loop


theorem kwLoopPhaseProduct_principal_sq
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D) :
    kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop ^ 2 = 1 := by
  rw [kwLoopPhaseProduct_principal_eq_branch]
  unfold kwLoopPhaseProduct
  rw [pow_two, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro k _
  rw [← pow_two, kwPrincipalHalfAngleBranch_sq]

theorem kwLoopPhaseProduct_principal_eq_one_or_neg_one
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D) :
    kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop = 1 ∨
      kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop = -1 :=
  sq_eq_one_iff.mp (kwLoopPhaseProduct_principal_sq angle loop)


theorem kwLoopPhaseProduct_eq_of_continuous_sign_homotopy
    {D : Type*} {n : ℕ} [NeZero n]
    (phase : ℝ → D → D → ℂ) (loop : Fin n → D)
    (hcontinuous : ∀ k : Fin n, ContinuousOn
      (fun t ↦ phase t (loop k) (loop (k + 1))) (Icc 0 1))
    (hsign : ∀ t ∈ Icc (0 : ℝ) 1,
      kwLoopPhaseProduct (phase t) loop = 1 ∨
        kwLoopPhaseProduct (phase t) loop = -1) :
    kwLoopPhaseProduct (phase 0) loop =
      kwLoopPhaseProduct (phase 1) loop := by
  let f : ℝ → ℂ := fun t ↦ kwLoopPhaseProduct (phase t) loop
  have hf : ContinuousOn f (Icc 0 1) := by
    dsimp only [f, kwLoopPhaseProduct]
    apply continuousOn_finsetProd
    intro k _
    exact hcontinuous k
  have hmaps : MapsTo f (Icc 0 1) ({1, -1} : Set ℂ) := by
    intro t ht
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hsign t ht
  exact isPreconnected_Icc.constant_of_mapsTo
    (Set.toFinite ({1, -1} : Set ℂ)).isDiscrete hf hmaps
    (by norm_num) (by norm_num)


theorem kwLoopPhaseProduct_principal_homotopy
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : ℝ → D → Real.Angle) (loop : Fin n → D)
    (hcontinuous : ∀ k : Fin n, ContinuousOn
      (fun t ↦ kwPrincipalHalfAnglePhase (angle t)
        (loop k) (loop (k + 1))) (Icc 0 1)) :
    kwLoopPhaseProduct (kwPrincipalHalfAnglePhase (angle 0)) loop =
      kwLoopPhaseProduct (kwPrincipalHalfAnglePhase (angle 1)) loop := by
  apply kwLoopPhaseProduct_eq_of_continuous_sign_homotopy
    (fun t ↦ kwPrincipalHalfAnglePhase (angle t)) loop hcontinuous
  intro t _
  exact kwLoopPhaseProduct_principal_eq_one_or_neg_one (angle t) loop


end StatMech.FrontierA
