/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDominationGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickInnerFaces.Part3
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part5
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Def.StatisticalMechanics.Code.FK.TriHexBrickDominationGeometry
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls

noncomputable section

noncomputable instance triHexBrickInnerBoundaryDecidable (N : Nat) :
    DecidablePred (triHexBrickInnerBoundary N) := Classical.decPred _


end
end StatMech.FK.PeriodicPlanar
