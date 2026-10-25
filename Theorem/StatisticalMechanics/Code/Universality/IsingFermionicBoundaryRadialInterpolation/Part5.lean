/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem finiteRadialGridInterpolant_cellPoint
    {m : Nat} (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin m → Fin m → Complex)
    (i j : Nat) (hi : i + 1 < m) (hj : j + 1 < m)
    (x y : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    finiteRadialGridInterpolant m mesh value
        (isingRadialGridCellPoint mesh i j x y) =
      complexBilinearCell
        (value ⟨i, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) x y := by
  classical
  unfold finiteRadialGridInterpolant
  rw [isingRadialGridCoordinate_cellPoint mesh hmesh i j x y]
  have hcast (u v : Real) : (((u * v : Real) : Complex)) =
      (u : Complex) * (v : Complex) := by push_cast; rfl
  simp_rw [hcast, mul_assoc]
  simp_rw [← Finset.mul_sum]
  rw [finite_sum_isingLinearTent_nat_add_mem_unit i hi x hx0 hx1]
  simp_rw [finite_sum_isingLinearTent_nat_add_mem_unit j hj y hy0 hy1]
  unfold complexBilinearCell
  push_cast
  ring

theorem finiteRadialGridInterpolant_continuous
    (m : Nat) (mesh : Real) (value : Fin m → Fin m → Complex) :
    Continuous (finiteRadialGridInterpolant m mesh value) := by
  unfold finiteRadialGridInterpolant isingRadialGridCoordinate
  apply continuous_finset_sum
  intro i _hi
  apply continuous_finset_sum
  intro j _hj
  have hx : Continuous (fun z : Complex =>
      z.re / mesh + z.im / mesh - 1 / 2 - (i.1 : Real)) := by
    fun_prop
  have hy : Continuous (fun z : Complex =>
      z.re / mesh - z.im / mesh - 1 / 2 - (j.1 : Real)) := by
    fun_prop
  exact (Complex.continuous_ofReal.comp
    ((isingLinearTent_continuous.comp hx).mul
      (isingLinearTent_continuous.comp hy))).mul continuous_const

@[simp] theorem finiteRadialGridInterpolant_position
    (m : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin m → Fin m → Complex) (i j : Fin m) :
    finiteRadialGridInterpolant m mesh value
        (isingRadialGridPosition mesh i.1 j.1) = value i j := by
  classical
  unfold finiteRadialGridInterpolant
  rw [isingRadialGridCoordinate_position mesh hmesh]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hbj
      rw [isingLinearTent_natCast_sub_eq_zero j.1 b.1 (by
        intro h
        apply hbj
        exact Fin.ext h.symm)]
      simp
    · simp
  · intro a _ha hai
    rw [isingLinearTent_natCast_sub_eq_zero i.1 a.1 (by
      intro h
      apply hai
      exact Fin.ext h.symm)]
    simp
  · simp


end
end StatMech.Universality
