/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding.Part2
import Theorem.StatisticalMechanics.Code.FK.SelfDualPointMassScore
import Theorem.StatisticalMechanics.Code.FK.BoundaryScoreLipschitz
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Abbrev.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def RlcTwoChannelDynamicRoutePlan.codeEquivPayload {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (route : P.Route) : P.Code route ≃ P.Payload route where
  toFun eta e := eta.1 e.1
  invFun bits :=
    ⟨fun e =>
      if hreserved : e ∈ P.reservedEdges route then true
      else if hslot : e ∈ P.payloadSlots route then bits ⟨e, hslot⟩
      else P.tagState route e,
    by
      constructor
      · intro e he
        simp [he]
      · intro e hreserved hslot
        simp [hreserved, hslot]⟩
  left_inv eta := by
    apply Subtype.ext
    funext e
    by_cases hreserved : e ∈ P.reservedEdges route
    · simp [hreserved, eta.2.1 e hreserved]
    · by_cases hslot : e ∈ P.payloadSlots route
      · simp [hreserved, hslot]
      · simp [hreserved, hslot, eta.2.2 e hreserved hslot]
  right_inv bits := by
    funext e
    have hreserved : e.1 ∉ P.reservedEdges route := by
      intro he
      exact Finset.disjoint_left.mp
        (P.reservedEdges_disjoint_payloadSlots route) he e.2
    simp [hreserved, e.2]


end
end StatMech.Universality
