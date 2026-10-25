/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionInfinite.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

@[simp] theorem isingCoordinateNegate_apply_same
    (i : Fin d) (x : Site d) : isingCoordinateNegate i x i = -x i := by
  simp [isingCoordinateNegate]

theorem isingCoordinateNegate_apply_of_ne
    (i a : Fin d) (hai : a ≠ i) (x : Site d) :
    isingCoordinateNegate i x a = x a := by
  simp [isingCoordinateNegate, hai]

@[simp] theorem isingCoordinateNegate_involutive
    (i : Fin d) (x : Site d) :
    isingCoordinateNegate i (isingCoordinateNegate i x) = x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp
  · simp [isingCoordinateNegate_apply_of_ne i a hai]

end StatMech.FrontierA
