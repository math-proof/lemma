/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineCurvature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part5
import Lemma.Set.IsBoundedImage.of.IsBounded.IsSimilitude
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.InnerProductSpace.Basic
open ChamberComplex

variable {V : Type*} [DecidableEq V]


namespace AffineBuilding

/-- A geodesic segment in a building from $x$ to $y$: a set of points
characterised by satisfying the parametrised distance equations
$d(p, x) = (1-t) d(x, y)$ and $d(p, y) = t d(x, y)$ for some $t \in [0, 1]$,
together with completeness (every such point is included). -/
structure GeodesicSegment (b : Building V) (md : ApartmentMetricData b)
    (x y : V) where
  points : Set V
  endpoints : x ∈ points ∧ y ∈ points
  dist_characterization : ∀ p ∈ points, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    buildingDist b md p x = (1 - t) * buildingDist b md x y ∧
    buildingDist b md p y = t * buildingDist b md x y
  complete : ∀ p : V, (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    buildingDist b md p x = (1 - t) * buildingDist b md x y ∧
    buildingDist b md p y = t * buildingDist b md x y) → p ∈ points

end AffineBuilding
