/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredReduction
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
open Finset
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem character_conj_mul_add
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (x z : IsingDyadicTorus d k) :
    conj (chi x) * chi (x + z) = chi z := by
  rw [AddChar.map_add_eq_mul, ← AddChar.inv_apply_eq_conj]
  have hne : chi x ≠ 0 := by
    intro hzero
    have hnorm := AddChar.norm_apply chi x
    simp [hzero] at hnorm
  field_simp

theorem character_spin_sum_normSq
    (u : IsingDyadicTorus d k → Real)
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    (Complex.normSq (∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x) :
        Complex) =
      ∑ x : IsingDyadicTorus d k, ∑ z : IsingDyadicTorus d k,
        ((u x * u (x + z) : Real) : Complex) * chi z := by
  rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul, Complex.conj_ofReal, Finset.mul_sum]
  calc
    ∑ y : IsingDyadicTorus d k,
        (u x : Complex) * conj (chi x) * ((u y : Complex) * chi y) =
      ∑ z : IsingDyadicTorus d k,
        (u x : Complex) * conj (chi x) *
          ((u (x + z) : Complex) * chi (x + z)) := by
      exact (Equiv.addLeft x).bijective.sum_comp
        (fun y : IsingDyadicTorus d k =>
          (u x : Complex) * conj (chi x) * ((u y : Complex) * chi y)) |>.symm
    _ = ∑ z : IsingDyadicTorus d k,
        ((u x * u (x + z) : Real) : Complex) * chi z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← character_conj_mul_add chi x z]
      push_cast
      ring


theorem finiteTorusFourierCoeff_isingTorusAveragedTwoPoint
    (beta : Real) (chi : AddChar (IsingDyadicTorus d k) Complex) :
    finiteTorusFourierCoeff
        (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi =
      ((∑ sigma : ConfigSpace (IsingDyadicTorus d k),
          Real.exp (-(beta / 2) *
            isingTorusDirichlet (isingTorusSpinField sigma)) *
          Complex.normSq (∑ x : IsingDyadicTorus d k,
            (isingTorusSpinField sigma x : Complex) * chi x)) /
        (isingTorusShiftedPartition (d := d) (k := k) beta 0 *
          Fintype.card (IsingDyadicTorus d k)) : Real) := by
  unfold finiteTorusFourierCoeff isingTorusAveragedTwoPoint
  push_cast
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun t : Complex => t /
    (isingTorusShiftedPartition (d := d) (k := k) beta 0 *
      Fintype.card (IsingDyadicTorus d k)))
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [character_spin_sum_normSq]
  push_cast
  calc
    ∑ z : IsingDyadicTorus d k,
        (Complex.exp (-((beta : Complex) / 2) *
            (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) *
          ∑ x : IsingDyadicTorus d k,
            (isingTorusSpinField sigma x : Complex) *
              isingTorusSpinField sigma (x + z)) * chi z =
      Complex.exp (-((beta : Complex) / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) *
        ∑ z : IsingDyadicTorus d k, ∑ x : IsingDyadicTorus d k,
          ((isingTorusSpinField sigma x *
            isingTorusSpinField sigma (x + z) : Real) : Complex) * chi z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [mul_assoc]
      rw [Finset.sum_mul]
      apply congrArg (fun t : Complex =>
        Complex.exp (-((beta : Complex) / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) * t)
      apply Finset.sum_congr rfl
      intro x _
      push_cast
      ring
    _ = Complex.exp (-((beta : Complex) / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) *
        ∑ x : IsingDyadicTorus d k, ∑ z : IsingDyadicTorus d k,
          ((isingTorusSpinField sigma x *
            isingTorusSpinField sigma (x + z) : Real) : Complex) * chi z := by
      rw [Finset.sum_comm]
    _ = Complex.exp (-((beta : Complex) / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) *
        ∑ x : IsingDyadicTorus d k, ∑ z : IsingDyadicTorus d k,
          (isingTorusSpinField sigma x : Complex) *
            isingTorusSpinField sigma (x + z) * chi z := by
      apply congrArg (fun t : Complex =>
        Complex.exp (-((beta : Complex) / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) * t)
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      push_cast
      rfl


theorem isingTorusAveragedTwoPoint_fourier_bound
    (beta : Real) (hbeta : 0 < beta)
    (hdom : IsingTorusGaussianDominated (d := d) (k := k) beta)
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (hdisp : 0 < isingTorusCharacterDispersion chi) :
    0 ≤ (finiteTorusFourierCoeff
        (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi).re ∧
      (finiteTorusFourierCoeff
          (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi).re ≤
        1 / (beta * isingTorusCharacterDispersion chi) := by
  let N : Real := ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma)) *
    Complex.normSq (∑ x : IsingDyadicTorus d k,
      (isingTorusSpinField sigma x : Complex) * chi x)
  let Z : Real := isingTorusShiftedPartition (d := d) (k := k) beta 0
  let card : Real := Fintype.card (IsingDyadicTorus d k)
  have hmode := isingTorus_addChar_secondMoment_le
    (d := d) (k := k) beta hbeta hdom chi hdisp
  have hZ : 0 < Z := isingTorusShiftedPartition_zero_pos beta
  have hcard : 0 < card := by
    dsimp [card]
    positivity
  have hden : 0 < Z * card := mul_pos hZ hcard
  have hN : 0 ≤ N := by
    exact Finset.sum_nonneg fun sigma _ =>
      mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _)
  rw [finiteTorusFourierCoeff_isingTorusAveragedTwoPoint]
  change 0 ≤ N / (Z * card) ∧
    N / (Z * card) ≤ 1 / (beta * isingTorusCharacterDispersion chi)
  refine ⟨div_nonneg hN hden.le, ?_⟩
  apply (div_le_iff₀ hden).2
  change N ≤ _
  change N ≤ Z *
    (Fintype.card (IsingDyadicTorus d k) /
      (beta * isingTorusCharacterDispersion chi)) at hmode
  calc
    N ≤ Z * (Fintype.card (IsingDyadicTorus d k) /
        (beta * isingTorusCharacterDispersion chi)) := hmode
    _ = 1 / (beta * isingTorusCharacterDispersion chi) * (Z * card) := by
      dsimp [card]
      ring

end StatMech.FrontierA
