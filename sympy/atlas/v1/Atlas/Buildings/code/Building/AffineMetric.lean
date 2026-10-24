/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Affine
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.CanonicalMetric
import Lemma.Real.IsWInvariantEuclideanDist
import Mathlib.Topology.MetricSpace.Basic

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter

/-- A map $f : X \to Y$ between pseudo-metric spaces is a similitude of
ratio $c > 0$ if $d(f(x), f(y)) = c \cdot d(x, y)$ for all $x, y \in X$. -/
def IsSimilitude {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (c : ℝ) : Prop :=
  0 < c ∧ ∀ x y : X, dist (f x) (f y) = c * dist x y

/-- A canonical metric on the realization of an affine Coxeter complex of
matrix $M$: a designated family of "chambers" $\{C\} \subseteq X$, each
bounded with diameter exactly $1$. -/
structure CanonicalMetric (M : CoxeterMatrix B) (X : Type*)
    [PseudoMetricSpace X] where
  chambers : Set (Set X)
  chamber_bounded : ∀ C ∈ chambers, Bornology.IsBounded C
  chamber_diam_one : ∀ C ∈ chambers, Metric.diam C = 1
  is_affine : M.IsAffine

/-- A canonical metric on $X$ is $W$-invariant under an action $W \times X
\to X$ if every $w \in W$ acts as an isometry on $X$. -/
def CanonicalMetric.IsWInvariant {M : CoxeterMatrix B} {X : Type*}
    [PseudoMetricSpace X]
    (_cm : CanonicalMetric M X)
    (action : M.Group → X → X) : Prop :=
  ∀ w : M.Group, ∀ x y : X, dist (action w x) (action w y) = dist x y

/-- The canonical distance on the Euclidean realization $E$ of an affine
Coxeter complex: $d(x, y) = \|x - y\| / \mathrm{diam}(C)$, where $C$ is
any chamber. This normalizes chambers to have diameter $1$. -/
noncomputable def CoxeterComplexCanonicalDist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : AffineCoxeterComplex E) (x y : E) : ℝ :=
  ‖x - y‖ / A.chamberDiameter

/-- The type of a per-apartment metric: a function assigning to each
apartment $A$ a (pseudo-)distance $V \times V \to \mathbb{R}$. -/
def apartmentMetric (b : Building V) :=
  { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → (V → V → ℝ)

/-- Per-apartment metric data for a building: an ambient space $X$ with
embedding $\iota : V \to X$ and a per-apartment pseudo-distance
$\mathrm{dist}_{\mathrm{fn}}$ that is symmetric, satisfies the triangle
inequality, vanishes on the diagonal, is preserved by every simplicial
isomorphism between apartments, and normalizes each chamber to have
diameter $1$. -/
structure ApartmentMetricData (b : Building V) where
  X : Type*
  ι : V → X
  dist_X : X → X → ℝ
  dist_fn : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → (V → V → ℝ)
  dist_nonneg : ∀ A x y, 0 ≤ dist_fn A x y
  dist_symm : ∀ A x y, dist_fn A x y = dist_fn A y x
  dist_eq_zero : ∀ A (x : V), dist_fn A x x = 0
  dist_triangle : ∀ A x y z, dist_fn A x z ≤ dist_fn A x y + dist_fn A y z
  iso_isometry : ∀ (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments }),
    ∀ (φ : SimplicialMap A₁.val A₂.val),
      (∀ s ∈ A₁.val.faces, s.image φ.toFun ∈ A₂.val.faces) →
      ∀ x y, dist_fn A₁ x y = dist_fn A₂ (φ.toFun x) (φ.toFun y)
  chamber_diam_one : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }),
    ∀ C, A.val.IsMaximal C →
      (∀ x ∈ C, ∀ y ∈ C, dist_fn A x y ≤ 1) ∧
      (∃ x ∈ C, ∃ y ∈ C, dist_fn A x y = 1)

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

/-- A "cross" version of well-definedness: $x$ lies in a shared face
$\sigma$ and $y$ lies in a shared chamber $C$; the two apartments share
both $\sigma$ and $C$, so an isomorphism fixes both $x$ and $y$ and the
apartment distances agree. -/
theorem buildingDist_wellDefined_from_face_and_chamber_cross
    (b : Building V) (md : ApartmentMetricData b)
    (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
    (σ : Finset V) (C : Finset V)
    (hσ_A₁ : σ ∈ A₁.val.faces) (hσ_A₂ : σ ∈ A₂.val.faces)
    (hC_max : A₁.val.IsMaximal C) (hC_A₂ : C ∈ A₂.val.faces)
    (x y : V) (hx_σ : x ∈ σ) (hy_C : y ∈ C) :
    md.dist_fn A₁ x y = md.dist_fn A₂ x y := by

  obtain ⟨φ, hφ_σ, hφ_C⟩ :=
    b.apartmentSystem.iso_exists A₁.val A₁.property A₂.val A₂.property
      σ hσ_A₁ hσ_A₂ C hC_max hC_A₂

  have hφx : φ.toFun x = x := hφ_σ x hx_σ
  have hφy : φ.toFun y = y := hφ_C y hy_C

  have h_iso := md.iso_isometry A₁ A₂ φ φ.map_face x y
  rw [h_iso, hφx, hφy]

/-- Well-definedness without assuming a common face: if vertices
$\{v\}, \{w\}$ are both vertices of two apartments $A_1, A_2$ (no shared
edge required), then $\mathrm{dist}_{A_1}(v, w) = \mathrm{dist}_{A_2}(v, w)$.
The proof combines $v$ and $w$ across a third apartment via the
"cross" lemma in both directions. -/
theorem buildingDist_well_defined_clean (b : Building V) (md : ApartmentMetricData b)
    (v w : V)
    (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
    (hv₁ : {v} ∈ A₁.val.faces) (hw₁ : {w} ∈ A₁.val.faces)
    (hv₂ : {v} ∈ A₂.val.faces) (hw₂ : {w} ∈ A₂.val.faces) :
    md.dist_fn A₁ v w = md.dist_fn A₂ v w := by

  obtain ⟨_, _, cc₁, hcc₁_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A₁.val A₁.property
  have hw_cc₁ : {w} ∈ cc₁.toSimplicialComplex.faces := hcc₁_eq ▸ hw₁
  obtain ⟨C_w, hCw_max_cc, hw_sub_Cw⟩ := cc₁.exists_maximal {w} hw_cc₁
  have hCw_max : A₁.val.IsMaximal C_w := hcc₁_eq ▸ hCw_max_cc
  have hCw_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A₁.val A₁.property C_w hCw_max

  obtain ⟨_, _, cc₂, hcc₂_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A₂.val A₂.property
  have hv_cc₂ : {v} ∈ cc₂.toSimplicialComplex.faces := hcc₂_eq ▸ hv₂
  obtain ⟨D_v, hDv_max_cc, hv_sub_Dv⟩ := cc₂.exists_maximal {v} hv_cc₂
  have hDv_max : A₂.val.IsMaximal D_v := hcc₂_eq ▸ hDv_max_cc
  have hDv_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A₂.val A₂.property D_v hDv_max

  obtain ⟨A₃_val, hA₃_mem, hCw_A₃, hDv_A₃⟩ :=
    b.apartmentSystem.contains_pair C_w D_v hCw_bmax hDv_bmax
  let A₃ : { A // A ∈ b.apartmentSystem.apartments } := ⟨A₃_val, hA₃_mem⟩

  have hv_A₃ : {v} ∈ A₃.val.faces :=
    A₃_val.down_closed hDv_A₃ hv_sub_Dv (Finset.singleton_nonempty v)
  have hw_A₃ : {w} ∈ A₃.val.faces :=
    A₃_val.down_closed hCw_A₃ hw_sub_Cw (Finset.singleton_nonempty w)

  have hw_in_Cw : w ∈ C_w := Finset.singleton_subset_iff.mp hw_sub_Cw
  have h₁ := buildingDist_wellDefined_from_face_and_chamber_cross b md A₁ A₃
    {v} C_w hv₁ hv_A₃ hCw_max hCw_A₃ v w
    (Finset.mem_singleton.mpr rfl) hw_in_Cw

  have hv_in_Dv : v ∈ D_v := Finset.singleton_subset_iff.mp hv_sub_Dv
  have h₂_swap := buildingDist_wellDefined_from_face_and_chamber_cross b md A₂ A₃
    {w} D_v hw₂ hw_A₃ hDv_max hDv_A₃ w v
    (Finset.mem_singleton.mpr rfl) hv_in_Dv

  have h₂ : md.dist_fn A₂ v w = md.dist_fn A₃ v w := by
    rw [md.dist_symm A₂ v w, h₂_swap, md.dist_symm A₃ w v]

  rw [h₁, ← h₂]

/-- The building distance defines a pseudo-metric: nonnegativity, symmetry,
$d(x, x) = 0$, and triangle inequality. -/
def IsMetricSpace (b : Building V) (md : ApartmentMetricData b) : Prop :=
  (∀ x y, 0 ≤ buildingDist b md x y) ∧
  (∀ x y, buildingDist b md x y = buildingDist b md y x) ∧
  (∀ x, buildingDist b md x x = 0) ∧
  (∀ x y z, buildingDist b md x z ≤ buildingDist b md x y + buildingDist b md y z)

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

end AffineBuilding
