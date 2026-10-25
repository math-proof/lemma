/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Structure.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem BdcTorusWindingToThinCover.planarLift_subset_longRectangleUnion
    {L alpha n : ℕ} [Fact (2 < L)]
    {W : Set (TorusAmbientConfig L)}
    (h : BdcTorusWindingToThinCover L alpha n W) :
    bdcTorusPlanarLiftEvent L W ⊆ bdcLongRectangleUnion alpha n := by
  rintro eta ⟨omega, homega, rfl⟩
  exact (bdcTorusThinCrossing_iff_pullback_mem_union
    L alpha n omega).mp (h.toThin omega homega)


end StatMech.BeffaraDC
