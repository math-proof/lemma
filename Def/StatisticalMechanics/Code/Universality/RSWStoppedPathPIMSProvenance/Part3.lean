/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide.Part3
import Structure.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcStoppedExtremalAxisGapProvenance.ofCandidate {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hselected : omega ∈ rlc_extremalPairCandidate (gamma, gamma'))
    (hselector : RlcAxisGapPIMSAnchoredContourSelector G hn hlt) :
    RlcStoppedExtremalAxisGapProvenance G hn hlt where
  selectedStratum := ⟨omega, hselected⟩
  anchoredSelector := hselector


end
end StatMech.Universality
