/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Instance.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part8
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelIndexedOuterConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')) :=
  fun e => if h : ∃ f,
      rlc_twoChannelIndexedOuterEdge gamma gamma' f = e then
    !(rlc_connectorForceTraceConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) h.choose.1)
  else decide
    (e ∈ (rlc_twoChannelIndexedSpokeGraph gamma gamma').edgeSet)

end
end StatMech.Universality
