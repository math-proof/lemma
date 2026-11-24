module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold.Part5
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFreeLeftContinuous
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionInfinite
open Filter MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionInfinite.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}


def isingMergeCoordinates
    (i j : Fin d) (x : Site d) : Site d :=
  fun a => if a = i then x i + x j else if a = j then 0 else x a

end StatMech.FrontierA
