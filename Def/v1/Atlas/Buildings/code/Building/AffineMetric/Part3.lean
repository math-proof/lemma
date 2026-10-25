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
import Structure.v1.Atlas.Buildings.code.Building.AffineMetric.Part2
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter


/-- The ambient-space distance between two vertices: $d_X(\iota v, \iota w)$. -/
def ApartmentMetricData.buildingDistVert {b : Building V}
    (md : ApartmentMetricData b) (v w : V) : ℝ :=
  md.dist_X (md.ι v) (md.ι w)

/-- The building distance between two vertices $x, y$: if there is some
apartment containing faces through both $x$ and $y$, return the
apartment-distance in any such apartment; otherwise return $0$.
Well-definedness is proved below by `buildingDist_well_defined_general`. -/
noncomputable def buildingDist (b : Building V) (md : ApartmentMetricData b)
    (x y : V) : ℝ :=
  if h : ∃ (A : { A // A ∈ b.apartmentSystem.apartments }),
      (∃ s ∈ A.val.faces, x ∈ s) ∧ (∃ s ∈ A.val.faces, y ∈ s)
  then md.dist_fn h.choose x y
  else 0

