/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide.Part3
import Structure.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def RlcSequentialExtremalExplorationState.ofNonempty
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hselected : (rlc_extremalPairCandidate (gamma, gamma')).Nonempty) :
    RlcSequentialExtremalExplorationState gamma gamma' where
  rawConfig := Classical.choose hselected
  selected := Classical.choose_spec hselected


end
end StatMech.Universality
