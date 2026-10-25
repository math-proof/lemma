/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Instance.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def hexCSPairPiece {T L : ℕ} (i : HexCSPairIndex T L) :
    Finset (HexCSIncidence T L) :=
  {i.1, hexCSReflectIncidence i.1}

def hexCSFixedPiece {T L : ℕ} {hT : 0 < T}
    (k : HexCSFixedIndex T L hT) : Finset (HexCSIncidence T L) :=
  {k.1}

def hexCSOrbitPiece {T L : ℕ} {hT : 0 < T}
    (o : HexCSPairIndex T L ⊕ HexCSFixedIndex T L hT) :
    Finset (HexCSIncidence T L) :=
  match o with
  | .inl i => hexCSPairPiece i
  | .inr k => hexCSFixedPiece k

end
end StatMech.Universality
