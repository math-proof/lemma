/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part4
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

def pfdOuterLeafWiredGraph (P : PlanarZ2Subgraph)
    (F : Set (kwg_Edge P)) : SimpleGraph (pfdOuterLeafVertex P) :=
  pfdOuterLeafOpenGraph P F ⊔
    boundaryCliqueGraph (pfdOuterLeafBoundary P)

end
end StatMech.FrontierD
