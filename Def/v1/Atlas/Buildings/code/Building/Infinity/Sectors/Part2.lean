/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part5
import Lemma.Set.IsBoundedImage.of.IsBounded.IsSimilitude
import Lemma.Finset.AreOpposite.of.AreOpposite
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import Def.v1.Atlas.Buildings.code.Building.Spherical
import Def.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
import Structure.v1.Atlas.Buildings.code.Building.Infinity.Sectors.Part2
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

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

end AffineBuilding
