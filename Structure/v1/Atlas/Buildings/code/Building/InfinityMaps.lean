/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part3
public import Theorem.Set.PointsAtInfinity.of.Vertices
public import Theorem.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
public import Def.v1.Atlas.Buildings.code.Building.Labels
public import Mathlib.Data.NNReal.Basic
public section

set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- A simplicial automorphism of a building $\mathcal{B}$: a bijection on
vertices that maps faces to faces and apartments to apartments. -/
structure IsSimplicialAutomorphism (b : Building V) (f : V → V) where
  maps_faces : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    s.image f ∈ b.toChamberComplex.toSimplicialComplex.faces
  bijective : Function.Bijective f
  maps_apartments : ∀ A ∈ b.apartmentSystem.apartments,
    ∃ A' ∈ b.apartmentSystem.apartments,
      ∀ s ∈ A.faces, s.image f ∈ A'.faces

/-- An isometry of the building's vertex set with respect to the apartment
metric: a vertex map $\varphi$ preserving the building distance. -/
structure BuildingIsometry (b : Building V) (md : ApartmentMetricData b) where
  toFun : V → V
  isometry : ∀ v w : V, buildingDist b md (toFun v) (toFun w) =
    buildingDist b md v w

end AffineBuilding
