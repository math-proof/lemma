/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Abbrev.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem bdcTorusVerticalWinding_planarLift_subset_longRectangleUnion
    {alpha n : ℕ} [Fact (2 < bdcLongRectanglePeriod alpha n)]
    (h : BdcTorusVerticalWindingThinCover alpha n) :
    bdcTorusPlanarLiftEvent (bdcLongRectanglePeriod alpha n)
        {omega |
          bdcTorusVerticalWinding (bdcLongRectanglePeriod alpha n) omega} ⊆
      bdcLongRectangleUnion alpha n :=
  h.planarLift_subset_longRectangleUnion

end StatMech.BeffaraDC
