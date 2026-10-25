/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide.Part3
import Def.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcSequentialExtremalExplorationState {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) where
  rawConfig : ConfigSpace (Sym2 (Site 2))
  selected : rawConfig ∈ rlc_extremalPairCandidate (gamma, gamma')


end
end StatMech.Universality
