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
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part2
open Finset
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusDirichletBilinearComplex_re
    (u : IsingDyadicTorus d k → Real)
    (v : IsingDyadicTorus d k → Complex) :
    (isingTorusDirichletBilinearComplex u v).re =
      isingTorusDirichletBilinear u (fun x => (v x).re) := by
  unfold isingTorusDirichletBilinearComplex isingTorusDirichletBilinear
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re]

theorem isingTorusDirichletBilinearComplex_im
    (u : IsingDyadicTorus d k → Real)
    (v : IsingDyadicTorus d k → Complex) :
    (isingTorusDirichletBilinearComplex u v).im =
      isingTorusDirichletBilinear u (fun x => (v x).im) := by
  unfold isingTorusDirichletBilinearComplex isingTorusDirichletBilinear
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_im]

theorem character_laplacian
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (x : IsingDyadicTorus d k) (i : Fin d) :
    2 * chi x - chi (x + isingTorusStep i) -
        chi (x - isingTorusStep i) =
      (Complex.normSq (1 - chi (isingTorusStep i)) : Complex) * chi x := by
  rw [AddChar.map_add_eq_mul, AddChar.map_sub_eq_div]
  rw [Complex.normSq_eq_conj_mul_self, map_sub, map_one,
    ← AddChar.inv_apply_eq_conj]
  have hne : chi (isingTorusStep i) ≠ 0 := by
    intro hzero
    have hnorm := AddChar.norm_apply chi (isingTorusStep i)
    simp [hzero] at hnorm
  field_simp
  ring

theorem sum_shift_character_edge
    (u : IsingDyadicTorus d k → Real)
    (chi : AddChar (IsingDyadicTorus d k) Complex) (i : Fin d) :
    (∑ x : IsingDyadicTorus d k,
        (u (x + isingTorusStep i) : Complex) *
          (chi x - chi (x + isingTorusStep i))) =
      ∑ x : IsingDyadicTorus d k, (u x : Complex) *
        (chi (x - isingTorusStep i) - chi x) := by
  let e : IsingDyadicTorus d k ≃ IsingDyadicTorus d k :=
    Equiv.addRight (-isingTorusStep i)
  calc
    (∑ x : IsingDyadicTorus d k,
        (u (x + isingTorusStep i) : Complex) *
          (chi x - chi (x + isingTorusStep i))) =
      ∑ x : IsingDyadicTorus d k,
        ((u ((e x) + isingTorusStep i) : Complex) *
          (chi (e x) - chi ((e x) + isingTorusStep i))) := by
        exact (e.sum_comp (fun x =>
          (u (x + isingTorusStep i) : Complex) *
            (chi x - chi (x + isingTorusStep i)))).symm
    _ = ∑ x : IsingDyadicTorus d k, (u x : Complex) *
        (chi (x - isingTorusStep i) - chi x) := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [e]
      simp [sub_eq_add_neg, add_assoc]


theorem isingTorusDirichletBilinearComplex_addChar
    (u : IsingDyadicTorus d k → Real)
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    isingTorusDirichletBilinearComplex u chi =
      (isingTorusCharacterDispersion chi : Complex) *
        ∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x := by
  unfold isingTorusDirichletBilinearComplex
  rw [Finset.sum_comm]
  calc
    ∑ i : Fin d, ∑ x : IsingDyadicTorus d k,
        ((u x : Complex) - u (x + isingTorusStep i)) *
          (chi x - chi (x + isingTorusStep i)) =
      ∑ i : Fin d, ∑ x : IsingDyadicTorus d k,
        (u x : Complex) *
          (2 * chi x - chi (x + isingTorusStep i) -
            chi (x - isingTorusStep i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, sum_shift_character_edge u chi i]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ i : Fin d, ∑ x : IsingDyadicTorus d k,
        (u x : Complex) *
          ((Complex.normSq (1 - chi (isingTorusStep i)) : Complex) * chi x) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      rw [character_laplacian chi x i]
    _ = (isingTorusCharacterDispersion chi : Complex) *
        ∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x := by
      simp only [isingTorusCharacterDispersion, Complex.ofReal_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem isingTorusDirichletBilinear_re_addChar
    (u : IsingDyadicTorus d k → Real)
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    isingTorusDirichletBilinear u (fun x => (chi x).re) =
      isingTorusCharacterDispersion chi *
        (∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x).re := by
  rw [← isingTorusDirichletBilinearComplex_re u chi,
    isingTorusDirichletBilinearComplex_addChar]
  simp

theorem isingTorusDirichletBilinear_im_addChar
    (u : IsingDyadicTorus d k → Real)
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    isingTorusDirichletBilinear u (fun x => (chi x).im) =
      isingTorusCharacterDispersion chi *
        (∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x).im := by
  rw [← isingTorusDirichletBilinearComplex_im u chi,
    isingTorusDirichletBilinearComplex_addChar]
  simp


theorem isingTorus_addChar_secondMoment_le
    (beta : Real) (hbeta : 0 < beta)
    (hdom : IsingTorusGaussianDominated (d := d) (k := k) beta)
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (hdisp : 0 < isingTorusCharacterDispersion chi) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Complex.normSq (∑ x : IsingDyadicTorus d k,
          (isingTorusSpinField sigma x : Complex) * chi x)) ≤
      isingTorusShiftedPartition (d := d) (k := k) beta 0 *
        (Fintype.card (IsingDyadicTorus d k) /
          (beta * isingTorusCharacterDispersion chi)) := by
  let hr : IsingDyadicTorus d k → Real := fun x => (chi x).re
  let hi : IsingDyadicTorus d k → Real := fun x => (chi x).im
  let W : ConfigSpace (IsingDyadicTorus d k) → Real := fun sigma =>
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma))
  let A : ConfigSpace (IsingDyadicTorus d k) → Complex := fun sigma =>
    ∑ x : IsingDyadicTorus d k,
      (isingTorusSpinField sigma x : Complex) * chi x
  let delta := isingTorusCharacterDispersion chi
  let Z := isingTorusShiftedPartition (d := d) (k := k) beta 0
  have hre := isingTorus_bilinear_secondMoment_le_dirichlet
    (d := d) (k := k) beta hbeta hdom hr
  have him := isingTorus_bilinear_secondMoment_le_dirichlet
    (d := d) (k := k) beta hbeta hdom hi
  have hbre (sigma) :
      isingTorusDirichletBilinear (isingTorusSpinField sigma) hr =
        delta * (A sigma).re := by
    exact isingTorusDirichletBilinear_re_addChar
      (isingTorusSpinField sigma) chi
  have hbim (sigma) :
      isingTorusDirichletBilinear (isingTorusSpinField sigma) hi =
        delta * (A sigma).im := by
    exact isingTorusDirichletBilinear_im_addChar
      (isingTorusSpinField sigma) chi
  change (∑ sigma, W sigma *
      (isingTorusDirichletBilinear
        (isingTorusSpinField sigma) hr) ^ 2) ≤
      Z * (isingTorusDirichlet hr / beta) at hre
  change (∑ sigma, W sigma *
      (isingTorusDirichletBilinear
        (isingTorusSpinField sigma) hi) ^ 2) ≤
      Z * (isingTorusDirichlet hi / beta) at him
  simp_rw [hbre] at hre
  simp_rw [hbim] at him
  have hsum : delta ^ 2 * (∑ sigma, W sigma * Complex.normSq (A sigma)) ≤
      Z * ((isingTorusDirichlet hr + isingTorusDirichlet hi) / beta) := by
    rw [Finset.mul_sum]
    calc
      ∑ sigma, delta ^ 2 * (W sigma * Complex.normSq (A sigma)) =
          (∑ sigma, W sigma * (delta * (A sigma).re) ^ 2) +
            ∑ sigma, W sigma * (delta * (A sigma).im) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro sigma _
        simp only [Complex.normSq_apply]
        ring
      _ ≤ Z * (isingTorusDirichlet hr / beta) +
          Z * (isingTorusDirichlet hi / beta) := add_le_add hre him
      _ = Z * ((isingTorusDirichlet hr + isingTorusDirichlet hi) / beta) := by
        ring
  have henergy : isingTorusDirichlet hr + isingTorusDirichlet hi =
      Fintype.card (IsingDyadicTorus d k) * delta :=
    isingTorusDirichlet_re_add_im_addChar chi
  rw [henergy] at hsum
  change (∑ sigma, W sigma * Complex.normSq (A sigma)) ≤ _
  rw [div_mul_eq_div_mul_one_div, div_eq_mul_inv]
  have hdelta : 0 < delta := hdisp
  have hdelta0 : delta ≠ 0 := hdelta.ne'
  calc
    (∑ sigma, W sigma * Complex.normSq (A sigma)) =
        delta ^ 2 * (∑ sigma, W sigma * Complex.normSq (A sigma)) /
          delta ^ 2 := by field_simp
    _ ≤ (Z * (Fintype.card (IsingDyadicTorus d k) * delta / beta)) /
          delta ^ 2 := by gcongr
    _ = Z * (Fintype.card (IsingDyadicTorus d k) * beta⁻¹ *
          (1 / delta)) := by field_simp


end StatMech.FrontierA
