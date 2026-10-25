/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part3
import Lemma.Set.PointsAtInfinity.of.Vertices
open AffineBuilding

variable {V : Type} [DecidableEq V]


/-- Bundles the spherical building at infinity $X_\infty$ together with its
simplicial complex structure: assembles the boundary $|X_\infty|$ from sectors,
verifying both sphericality and the simplicial-complex axioms (Sections 16.8–16.10). -/
noncomputable def buildingAtInfinity_full (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (h_nonempty : b.apartmentSystem.apartments.Nonempty) :
    SphericalSimplicialComplex b md :=
  buildBoundarySimplicialComplex b si md h_nonempty

