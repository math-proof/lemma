/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part3
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.Universality


theorem measurable_torusPlanarPullback (L : ℕ) [Fact (2 < L)] :
    Measurable (torusPlanarPullback L) :=
  measurable_of_finite _


theorem measurableEmbedding_torusPlanarPullback
    (L : ℕ) [Fact (2 < L)] :
    MeasurableEmbedding (torusPlanarPullback L) := by
  refine MeasurableEmbedding.mk (torusPlanarPullback_injective L)
    (measurable_torusPlanarPullback L) ?_
  intro A _hA
  exact (Set.toFinite A).image (torusPlanarPullback L) |>.measurableSet

end StatMech.BeffaraDC
