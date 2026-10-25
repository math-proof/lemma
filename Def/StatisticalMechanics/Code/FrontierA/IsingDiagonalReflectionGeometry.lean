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


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}


def isingDiagonalShift (i j : Fin d) (c : Int) : Site d :=
  fun a => if a = i then c else if a = j then -c else 0


def isingDiagonalReflect (i j : Fin d) (c : Int) (x : Site d) : Site d :=
  fun a => x (Equiv.swap i j a) + isingDiagonalShift i j c a

end StatMech.FrontierA
