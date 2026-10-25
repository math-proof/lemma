/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualBundles.Part2
import Theorem.StatisticalMechanics.Code.FK.IndexedEdgeLumping.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

instance pfdFullDualDecidableRel (P : PlanarZ2Subgraph) :
    DecidableRel (pfdClosedDual P ⊥).Adj := Classical.decRel _


end
end StatMech.FrontierD
