/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
open scoped BigOperators
open Finset SimpleGraph Polynomial


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Ising

universe u


theorem kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D) :
    kwLoopPhaseProduct
        (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop =
      Complex.exp
        ((((∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) : ℂ) *
          Complex.I) / 2) := by
  unfold kwLoopPhaseProduct kwAngleTurnPhase
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul, Finset.sum_div]


theorem kw_totalPrincipalTurn_eq_int_mul_two_pi
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D) :
    ∃ winding : ℤ,
      (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) =
        (winding : ℝ) * (2 * Real.pi) := by
  let s : ℝ := ∑ k,
    (angle (loop (k + 1)) - angle (loop k)).toReal
  have hcoe : (s : Real.Angle) = 0 := by
    calc
      (s : Real.Angle) =
          ∑ k, ((angle (loop (k + 1)) - angle (loop k)).toReal :
            Real.Angle) := by
        change Real.Angle.coeHom
          (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rfl
      _ = ∑ k, (angle (loop (k + 1)) - angle (loop k)) := by
        simp only [Real.Angle.coe_toReal]
      _ = 0 := by
        have hshift : (∑ k, angle (loop (k + 1))) =
            ∑ k, angle (loop k) := by
          change (∑ k, angle (loop ((Equiv.addRight (1 : Fin n)) k))) = _
          exact Equiv.sum_comp (Equiv.addRight (1 : Fin n))
            (fun k ↦ angle (loop k))
        rw [Finset.sum_sub_distrib, hshift, sub_self]
  obtain ⟨winding, hwinding⟩ := Real.Angle.coe_eq_zero_iff.mp hcoe
  refine ⟨winding, ?_⟩
  simpa only [s, zsmul_eq_mul] using hwinding.symm


theorem kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_odd_winding
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D)
    (winding : ℤ)
    (hturn :
      (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) =
        (winding : ℝ) * (2 * Real.pi))
    (hodd : Odd winding) :
    kwLoopPhaseProduct
        (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop =
      -1 := by
  rw [kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum, hturn]
  obtain ⟨k, rfl⟩ := hodd.exists_bit1
  rw [show
      ((((((2 * k + 1 : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) *
            Complex.I) / 2) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I by
      push_cast
      ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_pi_mul_I, one_mul]


theorem kw_odd_winding_of_angleTurnPhase_eq_neg_one
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D)
    (winding : ℤ)
    (hturn :
      (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) =
        (winding : ℝ) * (2 * Real.pi))
    (hphase : kwLoopPhaseProduct
      (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop = -1) :
    Odd winding := by
  apply Int.not_even_iff_odd.mp
  intro heven
  obtain ⟨k, hk⟩ := heven
  have hproduct := kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum angle loop
  rw [hphase, hturn] at hproduct
  have hexponent :
      (((((winding : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) / 2) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hk]
    push_cast
    ring
  rw [hexponent, Complex.exp_int_mul_two_pi_mul_I] at hproduct
  norm_num at hproduct


end StatMech.FrontierA
