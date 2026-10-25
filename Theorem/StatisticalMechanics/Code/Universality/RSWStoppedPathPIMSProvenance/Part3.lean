/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide.Part3
import Def.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_stoppedPIMSProvenance_of_extremalConstruction {n : Int}
    (hconstruction : RlcExtremalStrataCarryStoppedPIMSProvenance n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (hselected : (rlc_extremalPairCandidate (gamma, gamma')).Nonempty) :
    Nonempty (RlcStoppedExtremalAxisGapProvenance G hn hlt) :=
  hconstruction gamma gamma' G hn hlt hselected

end
end StatMech.Universality
