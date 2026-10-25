/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part2
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

instance pfdOuterLeafBoundaryDecidable (P : PlanarZ2Subgraph) :
    DecidablePred (pfdOuterLeafBoundary P) := fun x => by
  cases x <;> simp only [pfdOuterLeafBoundary] <;>
    exact Classical.propDecidable _


end
end StatMech.FrontierD
