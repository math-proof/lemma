/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_retainedChoiceAudit_right_vertices :
    rlc_pathVertices rlc_retainedChoiceAuditRight.1 =
      {![0, -2], ![1, -2], ![2, -2], ![2, -1], ![2, 0],
        ![1, 0], ![1, 1], ![2, 1], ![3, 1], ![4, 1]} := by
  simp [rlc_retainedChoiceAuditRight, rlc_pathVertices,
    rlc_rca_rightWalk, rlc_rca_rv,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

@[simp] theorem rlc_retainedChoiceAudit_left_vertices :
    rlc_pathVertices rlc_retainedChoiceAuditLeft.1 =
      {![-4, -2], ![-3, -2], ![-2, -2], ![-1, -2], ![-1, -1],
        ![-1, 0], ![-1, 1], ![-2, 1], ![-2, 2], ![-1, 2], ![0, 2]} := by
  simp [rlc_retainedChoiceAuditLeft, rlc_pathVertices,
    rlc_rca_leftWalk, rlc_rca_lv,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

end
end StatMech.Universality
