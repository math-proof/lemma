/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.AffineMetric
import Lemma.Set.IsBoundedImage.of.IsBounded.IsSimilitude
import Lemma.Finset.AreOpposite.of.AreOpposite
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import sympy.atlas.v1.Atlas.Buildings.code.Building.Spherical
import sympy.atlas.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection

set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- A *sector* in a Euclidean apartment $A$ of a building: a base vertex together with
a nonempty vertex set inside $A$, modeling a Weyl chamber (Section 16.5). -/
structure Sector (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  baseVertex : V
  baseVertex_mem : ∃ s ∈ apartment.faces, baseVertex ∈ s
  vertices : Set V
  vertices_in_apartment : ∀ v ∈ vertices, ∃ s ∈ apartment.faces, v ∈ s
  baseVertex_in_sector : baseVertex ∈ vertices
  nonempty : vertices.Nonempty

/-- Two sectors $S_1, S_2$ point in the same direction iff they have subsectors
$T_1 \subseteq S_1$ and $T_2 \subseteq S_2$ with $T_1.\text{vertices} = T_2.\text{vertices}$
— the parallelism relation underlying $X_\infty$ (Section 16.6). -/
def Sector.SameDirection (b : Building V) (S₁ S₂ : Sector b) : Prop :=
  ∃ (T₁ T₂ : Sector b),
    T₁.vertices ⊆ S₁.vertices ∧
    T₂.vertices ⊆ S₂.vertices ∧
    T₁.vertices = T₂.vertices

/-- A *direction*: the equivalence class of a sector under `SameDirection`, i.e. a
point of $X_\infty$ at the sector level. -/
def Sector.Direction (b : Building V) :=
  Quot (Sector.SameDirection b)

/-- $S'$ is a *subsector* of $S$: $S'.\text{vertices} \subseteq S.\text{vertices}$
and the two sectors share a direction. -/
def Sector.Subsector (b : Building V) (S' S : Sector b) : Prop :=
  S'.vertices ⊆ S.vertices ∧ Sector.SameDirection b S' S

/-- $S_1$ and $S_2$ are *opposite* sectors: same apartment, and they contain
subsectors sharing a common base vertex. -/
def Sector.IsOpposite (b : Building V) (S₁ S₂ : Sector b) : Prop :=
  S₁.apartment = S₂.apartment ∧
  ∃ (T₁ T₂ : Sector b),
    T₁.vertices ⊆ S₁.vertices ∧
    T₂.vertices ⊆ S₂.vertices ∧
    T₁.baseVertex = T₂.baseVertex

/-- A *geodesic ray* in the affine building: a map $ℕ → V$ that is an isometric
embedding for the building distance, $d(\rho(m), \rho(n)) = |m - n|$. -/
structure GeodesicRay (b : Building V) (md : ApartmentMetricData b) where
  toFun : ℕ → V
  isometry : ∀ m n : ℕ, buildingDist b md (toFun m) (toFun n) = ((m : ℤ) - (n : ℤ)).natAbs

/-- Two geodesic rays $\rho_1, \rho_2$ are *parallel* if $\sup_n d(\rho_1(n),\rho_2(n)) < \infty$
(bounded Hausdorff distance). -/
def GeodesicRay.Parallel (b : Building V) (md : ApartmentMetricData b)
    (ρ₁ ρ₂ : GeodesicRay b md) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, buildingDist b md (ρ₁.toFun n) (ρ₂.toFun n) ≤ C

/-- A *point at infinity* of the affine building: an equivalence class of
geodesic rays under parallelism. -/
def PointAtInfinity (b : Building V) (md : ApartmentMetricData b) :=
  Quot (GeodesicRay.Parallel b md)

/-- $S_\infty$: the set of points at infinity represented by geodesic rays that
remain entirely inside the sector $S$. -/
def Sector.pointsAtInfinity {b : Building V}
    (S : Sector b) (md : ApartmentMetricData b) :
    Set (PointAtInfinity b md) :=
  { p | ∃ (ρ : GeodesicRay b md), (∀ n, ρ.toFun n ∈ S.vertices) ∧
    p = Quot.mk (GeodesicRay.Parallel b md) ρ }

/-- Predicate: vertex $v$ belongs to some face of apartment $A$. -/
def VertexInApartment (A : SimplicialComplex V) (v : V) : Prop :=
  ∃ s ∈ A.faces, v ∈ s

/-- Predicate: every vertex of $S$ lies in some face of apartment $A$. -/
def SetInApartment (A : SimplicialComplex V) (S : Set V) : Prop :=
  ∀ v ∈ S, VertexInApartment A v

/-- Every face of an apartment extends to a maximal face (chamber) of that apartment. -/
theorem apt_face_extends_to_chamber_of_building (b : Building V) :
    ∀ (A : SimplicialComplex V), A ∈ b.apartmentSystem.apartments →
      ∀ s ∈ A.faces, ∃ D ∈ A.faces, A.IsMaximal D ∧ s ⊆ D := by
  intro A hA_mem s hs_face

  obtain ⟨_B_idx, _M, cc, hcc_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A hA_mem


  have hs_cc : s ∈ cc.faces := hcc_eq ▸ hs_face
  obtain ⟨C, hC_max, hs_sub_C⟩ := cc.exists_maximal s hs_cc

  have hC_max_A : A.IsMaximal C := hcc_eq ▸ hC_max
  exact ⟨C, hC_max_A.1, hC_max_A, hs_sub_C⟩

/-- Auxiliary axiomatic data needed to manipulate sectors: every apartment face
extends to a chamber, and the chamber containing a sector vertex is contained
in the sector. -/
structure SectorInfrastructure (_b : Building V) where
  apt_face_extends_to_chamber :
    ∀ (A : SimplicialComplex V), A ∈ _b.apartmentSystem.apartments →
      ∀ s ∈ A.faces, ∃ D ∈ A.faces, A.IsMaximal D ∧ s ⊆ D
  sector_chamber_closed :
    ∀ (S : Sector _b) (D : Finset V),
      D ∈ S.apartment.faces → S.apartment.IsMaximal D →
      (∃ v ∈ D, v ∈ S.vertices) → ∀ w ∈ D, w ∈ S.vertices

/-- Convenience constructor for `SectorInfrastructure` using the building-level
chamber extension lemma. -/
def SectorInfrastructure.mk' (b : Building V)
    (sector_chamber_closed :
      ∀ (S : Sector b) (D : Finset V),
        D ∈ S.apartment.faces → S.apartment.IsMaximal D →
        (∃ v ∈ D, v ∈ S.vertices) → ∀ w ∈ D, w ∈ S.vertices) :
    SectorInfrastructure b :=
  { apt_face_extends_to_chamber := apt_face_extends_to_chamber_of_building b
    sector_chamber_closed := sector_chamber_closed }
