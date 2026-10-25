/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part6
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem bdcLongRectangleTorusTranslationOriginIndex_mem
    (L alpha : ℕ) [NeZero L] (ha : 0 < alpha) :
    bdcLongRectangleTorusTranslationOriginIndex L alpha ha ∈
      bdcLongRectangleTorusTranslationIndices L alpha := by
  simp [bdcLongRectangleTorusTranslationIndices]

@[simp] theorem bdcLongRectangleTorusTranslationOriginIndex_event
    (L alpha n : ℕ) (ha : 0 < alpha) :
    bdcLongRectangleTorusTranslatedEvent L alpha n
        (bdcLongRectangleTorusTranslationOriginIndex L alpha ha) =
      bdcLongRectangleBaseEvent alpha n := by
  have hzero : bdcTorusCanonicalShift
      ((0, 0) : ZMod L × ZMod L) = (0 : Site 2) := by
    ext i
    fin_cases i <;> simp [bdcTorusCanonicalShift]
  rw [show bdcLongRectangleTorusTranslatedEvent L alpha n
      (bdcLongRectangleTorusTranslationOriginIndex L alpha ha) =
      translateConfig (bdcTorusCanonicalShift ((0, 0) : ZMod L × ZMod L)) ⁻¹'
        bdcLongRectangleEvent alpha n
          (bdcLongRectangleOriginIndex alpha ha) by rfl]
  rw [hzero, bdcLongRectangleOriginIndex_event]
  ext omega
  change translateConfig 0 omega ∈ bdcLongRectangleBaseEvent alpha n ↔
    omega ∈ bdcLongRectangleBaseEvent alpha n
  rw [translateConfig_zero]


end StatMech.BeffaraDC
