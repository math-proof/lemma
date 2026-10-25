/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_retainedChoiceAudit_right_edges :
    rlc_pathEdges rlc_retainedChoiceAuditRight.1 =
      rlc_rca_rightEdges := by
  simp [rlc_retainedChoiceAuditRight, rlc_pathEdges,
    rlc_rca_rightWalk, rlc_rca_rv, rlc_rca_rightEdges,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

end
end StatMech.Universality
