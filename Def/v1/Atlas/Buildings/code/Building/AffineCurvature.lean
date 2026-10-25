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
import Structure.v1.Atlas.Buildings.code.Building.AffineCurvature
open ChamberComplex

variable {V : Type*} [DecidableEq V]


namespace AffineBuilding

/-- The CAT(0) negative-curvature inequality: for any point $z$ and any geodesic
parametrisation $z_t = (1-t) x + t y$ (in terms of the building distance),
$d(z, z_t)^2 \le t\, d(z, x)^2 + (1-t)\, d(z, y)^2 - t(1-t)\, d(x, y)^2$. -/
def NegCurvatureIneq (b : Building V) (md : ApartmentMetricData b) : Prop :=
  ∀ (x y z z_t : V) (t : ℝ),
    0 ≤ t → t ≤ 1 →
    buildingDist b md z_t x = (1 - t) * buildingDist b md x y →
    buildingDist b md z_t y = t * buildingDist b md x y →
    (buildingDist b md z z_t) ^ 2 ≤
      t * (buildingDist b md z x) ^ 2 +
      (1 - t) * (buildingDist b md z y) ^ 2 -
      t * (1 - t) * (buildingDist b md x y) ^ 2

end AffineBuilding
