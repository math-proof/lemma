/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem mem_bdcTorusThinCrossingEvent
    (L alpha n : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    omega ∈ bdcTorusThinCrossingEvent L alpha n ↔
      bdcTorusThinCrossing L alpha n omega := by
  classical
  simp [bdcTorusThinCrossingEvent]


theorem bdcTorusThinCrossing_iff_pullback_mem_union
    (L alpha n : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    bdcTorusThinCrossing L alpha n omega ↔
      torusPlanarPullback L omega ∈ bdcLongRectangleUnion alpha n := by
  simp [bdcTorusThinCrossing, bdcLongRectangleUnion,
    bdcLongRectangleIndices, bdcLongRectangleEvent]


end StatMech.BeffaraDC
