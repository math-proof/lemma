/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContourDecomp.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11


namespace StatMech.Universality

open Complex

open scoped BigOperators


theorem hexFam_omega_cube : hexOmega ^ 3 = 1 := by
  unfold hexOmega
  rw [← Complex.exp_nat_mul]
  rw [show ((3 : ℕ) : ℂ) * (↑(2 * Real.pi / 3) * Complex.I) = (2 * Real.pi : ℂ) * Complex.I by
        push_cast; ring]
  exact Complex.exp_two_pi_mul_I


theorem hexFam_omega_ne_one : hexOmega ≠ 1 := by
  unfold hexOmega
  intro h
  have hre := congrArg Complex.re h
  rw [show (↑(2 * Real.pi / 3) * Complex.I) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by
        push_cast; ring] at hre
  rw [Complex.exp_ofReal_mul_I_re] at hre
  simp only [Complex.one_re] at hre
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
        Real.cos_pi_div_three]
  rw [hcos] at hre; norm_num at hre


theorem hexFam_omega_sum_zero : (1 : ℂ) + hexOmega + hexOmega ^ 2 = 0 := by
  have factored : (hexOmega - 1) * (1 + hexOmega + hexOmega ^ 2) = hexOmega ^ 3 - 1 := by ring
  rw [hexFam_omega_cube, sub_self] at factored
  rcases mul_eq_zero.mp factored with h | h
  · exact absurd (sub_eq_zero.mp h) hexFam_omega_ne_one
  · exact h


theorem hexFam_hexUnit_add_two (h : ℤ) : hexUnit (h + 2) = hexUnit h * hexOmega := by
  unfold hexUnit hexOmega
  rw [← Complex.exp_add]; congr 1; push_cast; ring


theorem hexFam_part5 {V : Type*} [DecidableEq V]
    (s : Finset (HexIncidence V)) (cls : HexIncidence V → Fin 5) :
    s = (s.filter (fun e => cls e = 0)) ∪ (s.filter (fun e => cls e = 1)) ∪
        (s.filter (fun e => cls e = 2)) ∪ (s.filter (fun e => cls e = 3)) ∪
        (s.filter (fun e => cls e = 4)) := by
  ext e
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro he
    have hcase : cls e = 0 ∨ cls e = 1 ∨ cls e = 2 ∨ cls e = 3 ∨ cls e = 4 := by omega
    tauto
  · rintro ((((⟨he, _⟩ | ⟨he, _⟩) | ⟨he, _⟩) | ⟨he, _⟩) | ⟨he, _⟩) <;> exact he


theorem hexFam_disj5 {V : Type*} [DecidableEq V]
    (s : Finset (HexIncidence V)) (cls : HexIncidence V → Fin 5) (a b : Fin 5) (hab : a ≠ b) :
    Disjoint (s.filter (fun e => cls e = a)) (s.filter (fun e => cls e = b)) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  simp only [Finset.mem_filter] at he1 he2
  exact hab (he1.2 ▸ he2.2)


end StatMech.Universality
