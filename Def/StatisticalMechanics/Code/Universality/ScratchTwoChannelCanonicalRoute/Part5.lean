/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelPIMSDiscardedEquivDiscarded_of_cover
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hcover : RlcTwoChannelPIMSCoversCentralEdges gamma gamma') :
    RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' ≃
      RlcTwoChannelDiscardedEdge gamma gamma' where
  toFun e := ⟨e.1, by
    intro hcentral
    let source :
        (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet :=
      ⟨e.1.1, hcentral⟩
    obtain ⟨target, htarget⟩ := hcover source
    let variableTarget : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
      ⟨target, by
        rw [htarget]
        exact rlc_centralFaceGraph_edge_site_mem source⟩
    apply e.2
    refine ⟨variableTarget, ?_⟩
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    rw [rlc_twoChannelPIMSSourceEdge_map, htarget]⟩
  invFun e := ⟨e.1, by
    rintro ⟨target, htarget⟩
    apply e.2
    rw [← htarget]
    exact rlc_twoChannelPIMSSourceEdge_mem_central target⟩
  left_inv e := rfl
  right_inv e := rfl

end
end StatMech.Universality
