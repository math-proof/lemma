/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part2


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}


theorem hypercubicLattice_adj_coordinateReflect
    (i : Fin d) (m : Int) (x y : Site d) :
    (hypercubicLattice d).Adj x y ↔
      (hypercubicLattice d).Adj
        (isingCoordinateReflect i m x) (isingCoordinateReflect i m y) := by
  change (∑ a, (x a - y a).natAbs) = 1 ↔
    (∑ a, (isingCoordinateReflect i m x a -
      isingCoordinateReflect i m y a).natAbs) = 1
  have hsum :
      (∑ a, (isingCoordinateReflect i m x a -
        isingCoordinateReflect i m y a).natAbs) =
        ∑ a, (x a - y a).natAbs := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases hai : a = i
    · subst a
      simp only [isingCoordinateReflect_apply_same]
      rw [show (m - x i) - (m - y i) = -(x i - y i) by ring,
        Int.natAbs_neg]
    · simp [isingCoordinateReflect_apply_of_ne i a hai]
  rw [hsum]

end StatMech.FrontierA
