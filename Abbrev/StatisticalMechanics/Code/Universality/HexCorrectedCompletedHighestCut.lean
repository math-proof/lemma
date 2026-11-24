module
public import Def.StatisticalMechanics.Code.Universality.HexCorrectedSideDepth
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedShiftedDivergence
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

noncomputable section

abbrev HexCSCompletedTopWalk (T : ℕ) (hT : 1 ≤ T) :=
  {ts : List ℤ // HexCSTopWalkAtWidth (T + 2) (by omega) ts}


end
end StatMech.Universality
