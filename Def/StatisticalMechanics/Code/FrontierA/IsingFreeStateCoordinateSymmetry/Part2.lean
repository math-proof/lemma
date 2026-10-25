/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionInfinite.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

def isingCoordinateNegate (i : Fin d) (x : Site d) : Site d :=
  fun a => if a = i then -x a else x a

end StatMech.FrontierA
