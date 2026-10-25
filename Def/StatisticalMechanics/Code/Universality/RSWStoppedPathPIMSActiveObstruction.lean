/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSScaleTwoAudit.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSActiveObstruction
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_activeGapDoubleFailureConfig :
    ConfigSpace (Sym2 (RlcConnectorVertex 1)) :=
  fun e => if e.map Subtype.val ∈
      ({s((![1, -1] : Site 2), ![1, 0]),
        s((![0, 0] : Site 2), ![1, 0]),
        s((![-1, 0] : Site 2), ![0, 0])} :
          Finset (Sym2 (Site 2))) then true else false

end
end StatMech.Universality
