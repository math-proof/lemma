/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part3
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.Universality


instance torusPlanarPushforward_isProbabilityMeasure
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    IsProbabilityMeasure (torusPlanarPushforward L hp hp1 hq) := by
  unfold torusPlanarPushforward
  exact inferInstance


end StatMech.BeffaraDC
