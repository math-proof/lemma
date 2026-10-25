/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionInfinite.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

def isingCoordinateNegateEquiv (i : Fin d) : Site d ≃ Site d where
  toFun := isingCoordinateNegate i
  invFun := isingCoordinateNegate i
  left_inv := isingCoordinateNegate_involutive i
  right_inv := isingCoordinateNegate_involutive i

end StatMech.FrontierA
