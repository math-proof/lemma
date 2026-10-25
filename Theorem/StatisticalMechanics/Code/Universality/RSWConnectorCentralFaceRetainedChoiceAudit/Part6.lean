/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_retainedChoiceAuditConfig_eq_true_iff
    (e : Sym2 (RlcConnectorVertex 2)) :
    rlc_retainedChoiceAuditConfig e = true ↔
      e.map Subtype.val ∈ rlc_retainedChoiceAuditOpenEdges := by
  simp [rlc_retainedChoiceAuditConfig]

end
end StatMech.Universality
