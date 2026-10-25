/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedFaithfulSubpath
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

abbrev RlcStrictAxisRightFullCrossing (n : Int) :=
  { gamma : RlcRightDiagonalPath n //
      ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 -> z 1 < 0 }


abbrev RlcStrictAxisLeftFullCrossing (n : Int) :=
  { gamma : RlcLeftDiagonalPath n //
      ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 -> 0 < z 1 }


abbrev RlcStrictAxisFullCrossingPair (n : Int) :=
  RlcStrictAxisRightFullCrossing n × RlcStrictAxisLeftFullCrossing n

end
end StatMech.Universality
