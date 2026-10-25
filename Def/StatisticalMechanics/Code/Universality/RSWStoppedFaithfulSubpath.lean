/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Instance.StatisticalMechanics.Code.Universality.RSWStoppedFaithfulSubpath
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_sourceExtremalPairCandidate {n : Int}
    (pair : RlcSourceFullCrossingPair n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_extremalPairCandidate (pair.1.1, pair.2.1)


noncomputable def rlc_sourceStoppedDiagonalEvent (n : Int) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ pair : RlcSourceFullCrossingPair n,
    rlc_sourceExtremalPairCandidate pair

end
end StatMech.Universality
