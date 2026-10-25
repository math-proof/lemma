/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBoxClusterUnion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareHoleFill.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FrontierB

noncomputable section

def squareBoxClusterUnion (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat) :
    Set (Site 2) :=
  ⋃ x ∈ box 2 n, cluster 2 omega x

end
end StatMech.FrontierD
