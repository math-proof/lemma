/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part2


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}


def isingCoordinatePlane (i : Fin d) (m : Int) (x : Site d) : Prop :=
  2 * x i = m

def isingCoordinateLower (i : Fin d) (m : Int) (x : Site d) : Prop :=
  2 * x i < m

end StatMech.FrontierA
