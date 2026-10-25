/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorTwoChannelGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y :=
    ((rlc_connectorCentralFaceFiniteGraph gamma gamma').Adj x y ∨
      (rlc_connectorReflectedTraceWiring gamma gamma').Adj x y) ∧
        ¬ (rlc_connectorTraceWiring gamma gamma').Adj x y
  symm := by
    constructor
    rintro x y ⟨hxy, hnot⟩
    exact ⟨hxy.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm),
      fun hyx => hnot hyx.symm⟩
  loopless := ⟨fun x hxx => hxx.1.elim
    (fun h => h.ne rfl) (fun h => h.ne rfl)⟩

end
end StatMech.Universality
