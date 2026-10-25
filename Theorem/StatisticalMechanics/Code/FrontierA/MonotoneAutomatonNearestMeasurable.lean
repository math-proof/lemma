/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestTransport.Part2
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem measurableSet_pairHighConnected (x y : Site d) :
    MeasurableSet {omega : PairSiteConfig d | y ∈ pairHighCluster omega x} := by
  exact (measurable_siteToBond.comp measurable_pairSiteRight)
    (measurableSet_connected x y)


theorem measurableSet_pairLowInfinite (x : Site d) :
    MeasurableSet {omega : PairSiteConfig d | x ∈ pairLowInfiniteVertices omega} := by
  exact (measurable_siteToBond.comp measurable_pairSiteLeft)
    (measurableSet_clusterInfinite x)


theorem measurableSet_pairHighInfinite (x : Site d) :
    MeasurableSet {omega : PairSiteConfig d |
      (pairHighCluster omega x).Infinite} := by
  exact (measurable_siteToBond.comp measurable_pairSiteRight)
    (measurableSet_clusterInfinite x)


end StatMech.FrontierA
