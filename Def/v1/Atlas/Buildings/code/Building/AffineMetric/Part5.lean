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
import Structure.v1.Atlas.Buildings.code.Building.AffineMetric.Part3
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter


/-- The building is a geodesic space: every pair of vertices is connected
by some geodesic path. -/
def IsGeodesic (b : Building V) (md : ApartmentMetricData b) : Prop :=
  ∀ x y, Nonempty (GeodesicPath b md x y)

/-- A retraction $\rho : V \to V$ is distance-non-increasing if
$d(\rho x, \rho y) \le d(x, y)$ for all vertices $x, y$. -/
def IsRetractDistNonIncreasing (b : Building V) (md : ApartmentMetricData b)
    (ρ : V → V) : Prop :=
  ∀ x y, buildingDist b md (ρ x) (ρ y) ≤ buildingDist b md x y

/-- A retraction $\rho : V \to V$ is an isometry on the base chamber if
$d(\rho x, \rho y) = d(x, y)$ whenever at least one of $x, y$ lies in the
base chamber. -/
def IsRetractIsometryOnBase (b : Building V) (md : ApartmentMetricData b)
    (ρ : V → V) (base : Finset V) : Prop :=
  ∀ x y, (x ∈ base ∨ y ∈ base) →
    buildingDist b md (ρ x) (ρ y) = buildingDist b md x y

/-- The (combinatorial) line segment from $x$ to $y$: the set of vertices
$z$ satisfying $d(x, y) = d(x, z) + d(z, y)$ (the additivity / "between"
relation). -/
def LineSegment (b : Building V) (md : ApartmentMetricData b) (x y : V) : Set V :=
  { z : V | buildingDist b md x y = buildingDist b md x z + buildingDist b md z y }

