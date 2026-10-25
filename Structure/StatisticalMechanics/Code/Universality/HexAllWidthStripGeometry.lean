/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Inductive.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

structure HexAWCoord where
  i : ℤ
  j : ℤ
  color : HexAWColor
  deriving DecidableEq, Repr


end
end StatMech.Universality
