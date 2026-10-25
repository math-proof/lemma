/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedFaithfulSubpath
import Instance.StatisticalMechanics.Code.Universality.RSWStrictAxisSourcePartition
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_strictAxisRightSourceEvent (n : Int) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ gamma : RlcStrictAxisRightFullCrossing n, rlc_pathOpen gamma.1.1


noncomputable def rlc_strictAxisLeftSourceEvent (n : Int) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ gamma : RlcStrictAxisLeftFullCrossing n, rlc_pathOpen gamma.1.1


noncomputable def rlc_strictAxisExtremalPairCandidate {n : Int}
    (pair : RlcStrictAxisFullCrossingPair n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_extremalPairCandidate (pair.1.1, pair.2.1)


noncomputable def rlc_strictAxisStoppedDiagonalEvent (n : Int) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ pair : RlcStrictAxisFullCrossingPair n,
    rlc_strictAxisExtremalPairCandidate pair


end
end StatMech.Universality
