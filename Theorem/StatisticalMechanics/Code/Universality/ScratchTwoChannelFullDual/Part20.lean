/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part24
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

@[simp] theorem rlc_twoChannelIndexedOuterConfig_randomEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedOuterConfig gamma gamma' omega
        (rlc_twoChannelIndexedOuterEdge gamma gamma' f) =
      !(rlc_connectorForceTraceConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1) := by
  unfold rlc_twoChannelIndexedOuterConfig
  split
  · rename_i h
    have hf : h.choose = f :=
      rlc_twoChannelIndexedOuterEdge_injective gamma gamma' h.choose_spec
    rw [hf]
  · rename_i h
    exact (h ⟨f, rfl⟩).elim


end
end StatMech.Universality
