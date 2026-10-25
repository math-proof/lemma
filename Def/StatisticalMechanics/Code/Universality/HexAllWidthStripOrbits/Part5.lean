/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Instance.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def hexAWPairPiece {T L : ℕ} (i : HexAWPairIndex T L) :
    Finset (HexAWIncidence T L) :=
  {i.1, hexAWReflectIncidence i.1}


def hexAWFixedPiece {T L : ℕ} {hT : 0 < T}
    (k : HexAWFixedIndex T L hT) : Finset (HexAWIncidence T L) :=
  {k.1}


def hexAWOrbitPiece {T L : ℕ} {hT : 0 < T}
    (o : HexAWPairIndex T L ⊕ HexAWFixedIndex T L hT) :
    Finset (HexAWIncidence T L) :=
  match o with
  | .inl i => hexAWPairPiece i
  | .inr k => hexAWFixedPiece k

end
end StatMech.Universality
