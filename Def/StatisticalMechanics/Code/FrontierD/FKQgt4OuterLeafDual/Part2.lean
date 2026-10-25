/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Instance.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

def pfdOuterLeafBoundary (P : PlanarZ2Subgraph) :
    pfdOuterLeafVertex P → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

end
end StatMech.FrontierD
