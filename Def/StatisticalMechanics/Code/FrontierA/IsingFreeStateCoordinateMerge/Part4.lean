/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge.Part3
open MeasureTheory


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}


def isingMergeFinset
    (i : Fin d) (S : Finset (Fin d)) (x : Site d) : Site d :=
  fun a => if a = i then x i + ∑ j ∈ S, x j
    else if a ∈ S then 0 else x a

end StatMech.FrontierA
