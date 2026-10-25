/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}


@[simp] theorem isingCoordinateReflect_apply_same
    (i : Fin d) (m : Int) (x : Site d) :
    isingCoordinateReflect i m x i = m - x i := by
  simp [isingCoordinateReflect]

theorem isingCoordinateReflect_apply_of_ne
    (i a : Fin d) (hai : a ≠ i) (m : Int) (x : Site d) :
    isingCoordinateReflect i m x a = x a := by
  simp [isingCoordinateReflect, hai]

@[simp] theorem isingCoordinateReflect_involutive
    (i : Fin d) (m : Int) (x : Site d) :
    isingCoordinateReflect i m (isingCoordinateReflect i m x) = x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp
  · simp [isingCoordinateReflect_apply_of_ne i a hai]

end StatMech.FrontierA
