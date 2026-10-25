/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3


namespace StatMech.Universality

open Complex HexWalk


def HexHeadingPeriodic (dregion : ℂ → ℤ → Prop) : Prop :=
  ∀ m h, dregion m h → dregion m (h + 6)


end StatMech.Universality
