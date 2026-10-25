/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part2


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

instance hexAWInStrip_decidable (T L : ℕ) (c : HexAWCoord) :
    Decidable (hexAWInStrip T L c) := by
  unfold hexAWInStrip hexAWBookRe2 hexAWBookSqrt3Im2
    hexAWDepth hexAWLong hexAWTrans
  infer_instance


end
end StatMech.Universality
