/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Abbrev.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

noncomputable instance pfdOuterLeafVertexFintype (P : PlanarZ2Subgraph) :
    Fintype (pfdOuterLeafVertex P) := Fintype.ofFinite _

noncomputable instance pfdOuterLeafVertexDecidableEq (P : PlanarZ2Subgraph) :
    DecidableEq (pfdOuterLeafVertex P) := Classical.decEq _


end
end StatMech.FrontierD
