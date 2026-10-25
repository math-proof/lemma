/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusPlusBoundaryField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusPlusBoundaryField
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

open StatMech.Percolation

noncomputable section

variable {d k R : Nat}


noncomputable def latticeNeighborLiftOfTorusAdj (x : Site d)
    (z : IsingDyadicTorus d k)
    (h : (isingTorusGraph d k).Adj (isingSiteToDyadicTorus k x) z) :
    Site d :=
  (exists_latticeNeighbor_lift_of_torusAdj x z h).choose

end
end StatMech.FrontierA
