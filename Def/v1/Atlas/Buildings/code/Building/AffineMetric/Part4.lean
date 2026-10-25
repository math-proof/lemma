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
import Theorem.v1.Atlas.Buildings.code.Building.AffineMetric
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter


/-- The building distance defines a pseudo-metric: nonnegativity, symmetry,
$d(x, x) = 0$, and triangle inequality. -/
def IsMetricSpace (b : Building V) (md : ApartmentMetricData b) : Prop :=
  (∀ x y, 0 ≤ buildingDist b md x y) ∧
  (∀ x y, buildingDist b md x y = buildingDist b md y x) ∧
  (∀ x, buildingDist b md x x = 0) ∧
  (∀ x y z, buildingDist b md x z ≤ buildingDist b md x y + buildingDist b md y z)

