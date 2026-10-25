/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

abbrev RlcSourceRightFullCrossing (n : Int) :=
  { gamma : RlcRightDiagonalPath n //
    (gamma.1.1 : Site 2) 1 < 0 ∧
      ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 ->
        z = (gamma.1.1 : Site 2) }


abbrev RlcSourceLeftFullCrossing (n : Int) :=
  { gamma : RlcLeftDiagonalPath n //
    0 < (gamma.1.2.1 : Site 2) 1 ∧
      ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 ->
        z = (gamma.1.2.1 : Site 2) }


abbrev RlcSourceFullCrossingPair (n : Int) :=
  RlcSourceRightFullCrossing n × RlcSourceLeftFullCrossing n

end
end StatMech.Universality
