/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingMarkovReflectionFold
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionGeometry


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}


@[simp] theorem isingDiagonalReflect_apply_i
    (i j : Fin d) (hij : i ≠ j) (c : Int) (x : Site d) :
    isingDiagonalReflect i j c x i = x j + c := by
  simp [isingDiagonalReflect, isingDiagonalShift, hij]

@[simp] theorem isingDiagonalReflect_apply_j
    (i j : Fin d) (hij : i ≠ j) (c : Int) (x : Site d) :
    isingDiagonalReflect i j c x j = x i - c := by
  simp [isingDiagonalReflect, isingDiagonalShift, Ne.symm hij, sub_eq_add_neg]

theorem isingDiagonalReflect_apply_of_ne
    (i j a : Fin d) (hai : a ≠ i) (haj : a ≠ j)
    (c : Int) (x : Site d) :
    isingDiagonalReflect i j c x a = x a := by
  simp [isingDiagonalReflect, isingDiagonalShift, hai, haj,
    Equiv.swap_apply_of_ne_of_ne]

@[simp] theorem isingDiagonalReflect_involutive
    (i j : Fin d) (hij : i ≠ j) (c : Int) (x : Site d) :
    isingDiagonalReflect i j c (isingDiagonalReflect i j c x) = x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [hij]
  · by_cases haj : a = j
    · subst a
      simp [hij, Ne.symm hij]
    · rw [isingDiagonalReflect_apply_of_ne i j a hai haj]
      rw [isingDiagonalReflect_apply_of_ne i j a hai haj]


end StatMech.FrontierA
