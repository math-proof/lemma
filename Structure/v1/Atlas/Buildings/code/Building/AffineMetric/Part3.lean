/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.AffineCoxeter.CanonicalMetric.Part2
import Lemma.Real.IsWInvariantEuclideanDist
import Mathlib.Topology.MetricSpace.Basic
import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part4
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter


/-- A geodesic path from $x$ to $y$ in the building: a finite vertex list
$v_0 = x, v_1, \ldots, v_n = y$ whose consecutive-distance sum equals
$\mathrm{dist}(x, y)$, certifying the path is length-minimizing. -/
structure GeodesicPath (b : Building V) (md : ApartmentMetricData b)
    (x y : V) where
  vertices : List V
  head_eq : vertices.head? = some x
  last_eq : vertices.getLast? = some y
  nonempty : vertices ≠ []
  length_eq : (List.zipWith (buildingDist b md) vertices vertices.tail).sum
    = buildingDist b md x y

