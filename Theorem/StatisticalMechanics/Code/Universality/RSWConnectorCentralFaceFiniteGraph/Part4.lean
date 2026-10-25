/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualFrame.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorCentralFaceAmbientConfig_support {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma') :
    rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e =
      rho (rlc_connectorCentralFaceEdgeLift e he) := by
  simp [rlc_connectorCentralFaceAmbientConfig, he]

@[simp] theorem rlc_connectorCentralFaceAmbientConfig_trace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true := by
  have hnot : e ∉ rlc_connectorCentralFaceEdges gamma gamma' := by
    intro hrandom
    apply (Finset.mem_sdiff.mp hrandom).2
    exact Finset.mem_union_left _ he
  simp [rlc_connectorCentralFaceAmbientConfig, hnot, he]

theorem rlc_connectorCentralFaceAmbientConfig_eq_false_of_lifts_closed
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (htrace : e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
    (hclosed : ∀ f : Sym2 (RlcConnectorVertex n),
      f.map Subtype.val = e → rho f = false) :
    rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = false := by
  unfold rlc_connectorCentralFaceAmbientConfig
  split
  · rename_i he
    exact hclosed _ (rlc_connectorCentralFaceEdgeLift_map e he)
  · simp [htrace]


end
end StatMech.Universality
