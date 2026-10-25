/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


theorem hexPhase_sideTilt_reflect_one (h : ℤ) :
    hexPhase_sideTilt (2 - h) = -hexPhase_sideTilt h := by
  unfold hexPhase_sideTilt
  push_cast
  ring


end StatMech.Universality
