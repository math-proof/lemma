/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_rca_faceRegion : Finset (Site 2) :=
  {![0, 1], ![-1, -1], ![-1, -2], ![0, 0], ![-1, 1],
    ![1, 1], ![-2, 1], ![0, -2], ![-1, 0], ![0, -1]}

def rlc_rca_regionWallEdges : Finset (Sym2 (Site 2)) :=
  {s(![-1, -1], ![-1, 0]), s(![-1, -2], ![-1, -1]),
    s(![1, 0], ![1, 1]), s(![2, 1], ![2, 2]),
    s(![1, 1], ![2, 1]), s(![-2, 1], ![-2, 2]),
    s(![-2, 1], ![-1, 1]), s(![1, -2], ![1, -1]),
    s(![-1, 0], ![-1, 1]), s(![1, -1], ![1, 0])}

end
end StatMech.Universality
