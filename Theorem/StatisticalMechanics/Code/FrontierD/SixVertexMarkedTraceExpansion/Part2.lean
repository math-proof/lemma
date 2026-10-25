/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Mathlib.Algebra.Polynomial.Eval.Degree
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

open Polynomial


theorem Polynomial.coeffNonnegative_zero :
    Polynomial.CoeffNonnegative (0 : Real[X]) := by
  intro k
  simp

theorem Polynomial.coeffNonnegative_one :
    Polynomial.CoeffNonnegative (1 : Real[X]) := by
  intro k
  simp only [Polynomial.coeff_one]
  split <;> positivity

theorem Polynomial.coeffNonnegative_add
    {p q : Real[X]} (hp : Polynomial.CoeffNonnegative p)
    (hq : Polynomial.CoeffNonnegative q) :
    Polynomial.CoeffNonnegative (p + q) := by
  intro k
  rw [Polynomial.coeff_add]
  exact add_nonneg (hp k) (hq k)

theorem Polynomial.coeffNonnegative_mul
    {p q : Real[X]} (hp : Polynomial.CoeffNonnegative p)
    (hq : Polynomial.CoeffNonnegative q) :
    Polynomial.CoeffNonnegative (p * q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hp ij.1) (hq ij.2)

theorem Polynomial.coeffNonnegative_pow
    {p : Real[X]} (hp : Polynomial.CoeffNonnegative p) (m : Nat) :
    Polynomial.CoeffNonnegative (p ^ m) := by
  induction m with
  | zero => exact Polynomial.coeffNonnegative_one
  | succ m ih =>
      rw [pow_succ]
      exact Polynomial.coeffNonnegative_mul ih hp

theorem Polynomial.coeffNonnegative_sum
    {alpha : Type*} (s : Finset alpha) (f : alpha -> Real[X])
    (hf : ∀ i ∈ s, Polynomial.CoeffNonnegative (f i)) :
    Polynomial.CoeffNonnegative (∑ i ∈ s, f i) := by
  intro k
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  exact Finset.sum_nonneg fun i hi => hf i hi k

theorem Polynomial.coeffNonnegative_two_add_X :
    Polynomial.CoeffNonnegative (C 2 + X : Real[X]) := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    norm_num
  · by_cases hk1 : k = 1
    · subst k
      norm_num
    · have hk1' : 1 ≠ k := Ne.symm hk1
      simp [Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_X, hk0, hk1']

theorem sixVertexShiftedSectorTransferPolynomial_coeffNonnegative
    (N n : Nat) (x y : SixVertexSector N n) :
    Polynomial.CoeffNonnegative
      (sixVertexShiftedSectorTransferPolynomial N n x y) := by
  classical
  unfold sixVertexShiftedSectorTransferPolynomial
  split
  · intro k
    by_cases hk : k = 0
    · subst k
      norm_num
    · simp [Polynomial.coeff_C, hk]
  · split
    · exact Polynomial.coeffNonnegative_pow
        Polynomial.coeffNonnegative_two_add_X _
    · exact Polynomial.coeffNonnegative_zero

theorem sixVertexShiftedSectorTransferPolynomial_pow_coeffNonnegative
    (N n M : Nat) (x y : SixVertexSector N n) :
    Polynomial.CoeffNonnegative
      ((sixVertexShiftedSectorTransferPolynomial N n ^ M) x y) := by
  induction M generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      split
      · exact Polynomial.coeffNonnegative_one
      · exact Polynomial.coeffNonnegative_zero
  | succ M ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Polynomial.coeffNonnegative_sum
      intro z hz
      exact Polynomial.coeffNonnegative_mul (ih x z)
        (sixVertexShiftedSectorTransferPolynomial_coeffNonnegative N n z y)


end
end StatMech.FrontierD
