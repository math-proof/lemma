/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingLinearTent_continuous : Continuous isingLinearTent := by
  unfold isingLinearTent
  fun_prop

@[simp] theorem isingLinearTent_zero : isingLinearTent 0 = 1 := by
  simp [isingLinearTent]

theorem isingLinearTent_natCast_sub_eq_zero
    (i j : Nat) (hij : i ≠ j) :
    isingLinearTent ((i : Real) - (j : Real)) = 0 := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hle : (i : Real) - (j : Real) ≤ -1 := by exact_mod_cast (show (i : Int) - j ≤ -1 by omega)
    have habs : 1 ≤ |(i : Real) - (j : Real)| := by
      rw [abs_of_nonpos (hle.trans (by norm_num))]
      linarith
    unfold isingLinearTent
    rw [max_eq_left (sub_nonpos.mpr habs)]
  · have hle : (j : Real) - (i : Real) ≤ -1 := by
      exact_mod_cast (show (j : Int) - i ≤ -1 by omega)
    have hpos : 1 ≤ (i : Real) - (j : Real) := by linarith
    have habs : 1 ≤ |(i : Real) - (j : Real)| := by
      rw [abs_of_nonneg (by linarith)]
      exact hpos
    unfold isingLinearTent
    rw [max_eq_left (sub_nonpos.mpr habs)]

theorem isingLinearTent_eq_one_sub_of_mem_unit
    (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    isingLinearTent x = 1 - x := by
  simp [isingLinearTent, abs_of_nonneg hx0, hx1]

theorem isingLinearTent_sub_one_eq_of_mem_unit
    (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    isingLinearTent (x - 1) = x := by
  simp [isingLinearTent, abs_of_nonpos (sub_nonpos.mpr hx1), hx0]


theorem isingLinearTent_nat_add_mem_unit_sub_eq_zero
    (i a : Nat) (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hai : a ≠ i) (hai1 : a ≠ i + 1) :
    isingLinearTent ((i : Real) + x - (a : Real)) = 0 := by
  rcases lt_or_gt_of_ne hai with ha | ha
  · have hcast : (a : Real) + 1 ≤ (i : Real) := by
      exact_mod_cast (show a + 1 ≤ i by omega)
    have habs : 1 ≤ |(i : Real) + x - (a : Real)| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    simp [isingLinearTent, habs]
  · have hai2 : i + 2 ≤ a := by omega
    have hcast : (i : Real) + 2 ≤ (a : Real) := by exact_mod_cast hai2
    have habs : 1 ≤ |(i : Real) + x - (a : Real)| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    simp [isingLinearTent, habs]


theorem finite_sum_isingLinearTent_nat_add_mem_unit
    {m : Nat} (i : Nat) (hi : i + 1 < m)
    (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (f : Fin m → Complex) :
    ∑ a : Fin m,
        ((isingLinearTent ((i : Real) + x - (a.1 : Real)) : Real) : Complex) * f a =
      (((1 - x : Real) : Complex) * f ⟨i, by omega⟩ +
        ((x : Real) : Complex) * f ⟨i + 1, by omega⟩) := by
  classical
  let i0 : Fin m := ⟨i, by omega⟩
  let i1 : Fin m := ⟨i + 1, by omega⟩
  rw [← Finset.sum_subset (s₁ := {i0, i1}) (s₂ := Finset.univ)]
  · simp [i0, i1, isingLinearTent_eq_one_sub_of_mem_unit x hx0 hx1,
      isingLinearTent_sub_one_eq_of_mem_unit x hx0 hx1]
  · simp
  · intro a _ha ha
    have hai : a.1 ≠ i := by
      intro h
      apply ha
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      apply Fin.ext
      simpa [i0] using h
    have hai1 : a.1 ≠ i + 1 := by
      intro h
      apply ha
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      apply Fin.ext
      simpa [i1] using h
    rw [isingLinearTent_nat_add_mem_unit_sub_eq_zero
      i a.1 x hx0 hx1 hai hai1]
    simp


end
end StatMech.Universality
