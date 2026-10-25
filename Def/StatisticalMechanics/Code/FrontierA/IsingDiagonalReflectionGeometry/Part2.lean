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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionGeometry


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}


def isingDiagonalReflectEquiv
    (i j : Fin d) (hij : i ≠ j) (c : Int) : Site d ≃ Site d where
  toFun := isingDiagonalReflect i j c
  invFun := isingDiagonalReflect i j c
  left_inv := isingDiagonalReflect_involutive i j hij c
  right_inv := isingDiagonalReflect_involutive i j hij c

end StatMech.FrontierA
