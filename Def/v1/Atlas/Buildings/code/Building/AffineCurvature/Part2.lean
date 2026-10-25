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
import Structure.v1.Atlas.Buildings.code.Building.AffineCurvature.Part2
open ChamberComplex

variable {V : Type*} [DecidableEq V]


namespace AffineBuilding

/-- The building is contractible: there is a base point $y_0$ and a homotopy
$f : [0,1] \times \mathcal{B} \to \mathcal{B}$ with $f(1, \cdot) = \mathrm{id}$,
$f(0, \cdot) = y_0$, geodesic-distance constraints, and joint continuity
in $(t, x)$. -/
def IsContractible (b : Building V) (md : ApartmentMetricData b) : Prop :=
  ∃ (y₀ : V) (f : ℝ → V → V),

    (∀ x, f 1 x = x) ∧

    (∀ x, f 0 x = y₀) ∧

    (∀ (t : ℝ) (x : V), 0 ≤ t → t ≤ 1 →
      buildingDist b md (f t x) x = (1 - t) * buildingDist b md x y₀ ∧
      buildingDist b md (f t x) y₀ = t * buildingDist b md x y₀) ∧

    (∀ (t : ℝ) (x : V) (ε : ℝ), 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (t' : ℝ) (x' : V),
          |t' - t| < δ → buildingDist b md x' x < δ →
          buildingDist b md (f t' x') (f t x) < ε)

/-- The building is complete: every Cauchy sequence of vertices converges to a
limit in $V$. -/
def IsComplete (b : Building V) (md : ApartmentMetricData b) : Prop :=
  ∀ (seq : ℕ → V),

    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      buildingDist b md (seq m) (seq n) < ε) →

    ∃ lim : V, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      buildingDist b md (seq n) lim < ε

end AffineBuilding
