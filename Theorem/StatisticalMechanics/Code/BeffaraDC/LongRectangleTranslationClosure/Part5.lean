/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part4
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem bdcLongRectangleTorusTranslationIndex_card
    (L alpha : ℕ) [NeZero L] :
    Fintype.card (BdcLongRectangleTorusTranslationIndex L alpha) =
      L ^ 2 * (2 * alpha ^ 3) := by
  simp [BdcLongRectangleIndex]
  ring


end StatMech.BeffaraDC
