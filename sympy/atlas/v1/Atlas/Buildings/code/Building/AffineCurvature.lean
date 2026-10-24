/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineCurvature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.AffineMetric
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

/-- A building $(\mathcal{B}, d)$ is CAT(0) if it is a complete geodesic metric
space satisfying the negative-curvature (CAT(0)) inequality on every geodesic
triangle. This is the geometric form of "non-positive curvature". -/
structure IsCAT0 (b : Building V) (md : ApartmentMetricData b) : Prop where
  metric : IsMetricSpace b md
  geodesic : IsGeodesic b md
  neg_curvature : NegCurvatureIneq b md

/-- Data realising each apartment of a building as an isometric copy of a
Euclidean (inner product) space $E$: coordinates, the distance-as-norm
identity, and the fact that the geodesic point in the apartment maps to the
Euclidean barycentric combination. -/
structure EuclideanRealizationData {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : Building V) (md : ApartmentMetricData b) where
  coord : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → V → E
  dist_eq_norm : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }) (u v : V),
    md.dist_fn A u v = ‖coord A u - coord A v‖
  coord_geodesic : ∀ (A : { A // A ∈ b.apartmentSystem.apartments })
    (x y z_t : V) (t : ℝ),
    (∃ s ∈ A.val.faces, x ∈ s) → (∃ s ∈ A.val.faces, y ∈ s) →
    (∃ s ∈ A.val.faces, z_t ∈ s) →
    md.dist_fn A z_t x = (1 - t) * md.dist_fn A x y →
    md.dist_fn A z_t y = t * md.dist_fn A x y →
    coord A z_t = t • coord A x + (1 - t) • coord A y

/-- Data witnessing that a building admits suitable retractions: for any four
vertices $x, y, z, z_t$ there is a distance-non-increasing retraction $\rho$
to an apartment $A$ containing $x$, $y$, $\rho z$ and fixing $x$ and $y$,
together with the assertion that a geodesic point $z_t$ remains in any
apartment containing both endpoints. -/
structure BuildingRetractionData (b : Building V) (md : ApartmentMetricData b) where
  retract_exists : ∀ (x y z z_t : V),
    ∃ (ρ : V → V) (A : { A // A ∈ b.apartmentSystem.apartments }),
      (∃ s ∈ A.val.faces, x ∈ s) ∧ (∃ s ∈ A.val.faces, y ∈ s) ∧
      (∃ s ∈ A.val.faces, ρ z ∈ s) ∧
      ρ x = x ∧ ρ y = y ∧
      (∀ u v, buildingDist b md (ρ u) (ρ v) ≤ buildingDist b md u v) ∧
      buildingDist b md z z_t = buildingDist b md (ρ z) z_t
  zt_in_apt : ∀ (x y z_t : V) (t : ℝ),
    0 ≤ t → t ≤ 1 →
    buildingDist b md z_t x = (1 - t) * buildingDist b md x y →
    buildingDist b md z_t y = t * buildingDist b md x y →
    ∀ (A : { A // A ∈ b.apartmentSystem.apartments }),
      (∃ s ∈ A.val.faces, x ∈ s) → (∃ s ∈ A.val.faces, y ∈ s) →
      (∃ s ∈ A.val.faces, z_t ∈ s)

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
