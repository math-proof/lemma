/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_retainedChoiceAuditOpenEdges : Finset (Sym2 (Site 2)) :=
  {s(![0, -1], ![1, -1]), s(![-1, 1], ![0, 1]),
    s(![0, 0], ![1, 0]), s(![-1, -1], ![0, -1])}

def rlc_retainedChoiceAuditConfig :
    ConfigSpace (Sym2 (RlcConnectorVertex 2)) :=
  fun e => if e.map Subtype.val ∈ rlc_retainedChoiceAuditOpenEdges
    then true else false

end
end StatMech.Universality
