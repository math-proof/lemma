/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}


def isingCoordinateReflectEquiv
    (i : Fin d) (m : Int) : Site d ≃ Site d where
  toFun := isingCoordinateReflect i m
  invFun := isingCoordinateReflect i m
  left_inv := isingCoordinateReflect_involutive i m
  right_inv := isingCoordinateReflect_involutive i m

end StatMech.FrontierA
