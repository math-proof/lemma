/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCutGeometry.Part3


namespace StatMech.Universality

open HexWalk

public noncomputable section

set_option maxHeartbeats 800000 in


structure HexCSHighestCutGeometry (T : ℕ) (hT : 1 ≤ T) where
  cut : ∀ d : {ts : List ℤ // HexCSNewSideWalk T hT ts},
    HexCSCutData (T + 1) (by omega) d.1

end
end StatMech.Universality
