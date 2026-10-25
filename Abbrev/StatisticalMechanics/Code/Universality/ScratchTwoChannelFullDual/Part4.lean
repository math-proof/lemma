/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part13
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

abbrev RlcTwoChannelFullVisibleSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    source ∈ Set.range
      (rlc_twoChannelFullSourceEdge (gamma := gamma) (gamma' := gamma'))}

abbrev RlcTwoChannelFullDiscardedSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    source ∉ Set.range
      (rlc_twoChannelFullSourceEdge (gamma := gamma) (gamma' := gamma'))}


end
end StatMech.Universality
