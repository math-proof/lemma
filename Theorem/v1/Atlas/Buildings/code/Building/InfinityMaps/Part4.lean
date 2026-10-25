/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part3
import Lemma.Set.PointsAtInfinity.of.Vertices
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Def.v1.Atlas.Buildings.code.Building.Labels
import Mathlib.Data.NNReal.Basic
import Def.v1.Atlas.Buildings.code.Building.InfinityMaps.Part5
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Every automorphism induces a well-defined map on $X_\infty$: each
simplex at infinity has an image simplex whose points are the $\varphi_\infty$
images of the original. -/
theorem inducedSimplexMap_exists
    {b : Building V} {md : ApartmentMetricData b}
    (f : V → V) (hf : IsSimplicialAutomorphism b f)
    (σ : SimplexAtInfinity b md) :
    ∃ (τ : SimplexAtInfinity b md),
      τ.points = (isometryOfAutomorphism md f hf).inducedMapInfinity '' σ.points := by
  obtain ⟨S, hS⟩ := σ.from_sector
  obtain ⟨S', hS'⟩ := automorphism_maps_sectors f hf S
  have h_image_subset :
      (isometryOfAutomorphism md f hf).inducedMapInfinity '' σ.points ⊆
        S'.pointsAtInfinity md := by
    intro p hp
    obtain ⟨q, hq_mem, hq_eq⟩ := hp
    have hq_in_S : q ∈ S.pointsAtInfinity md := hS hq_mem
    simp only [Sector.pointsAtInfinity, Set.mem_setOf_eq] at hq_in_S ⊢
    obtain ⟨ρ, hρ_in_S, hq_is_ρ⟩ := hq_in_S
    subst hq_is_ρ
    rw [BuildingIsometry.inducedMapInfinity_mk] at hq_eq
    refine ⟨(isometryOfAutomorphism md f hf).pushforwardRay ρ, ?_, hq_eq.symm⟩
    intro n
    simp only [BuildingIsometry.pushforwardRay, isometryOfAutomorphism, Function.comp]
    rw [hS']
    exact ⟨ρ.toFun n, hρ_in_S n, rfl⟩
  exact ⟨⟨(isometryOfAutomorphism md f hf).inducedMapInfinity '' σ.points,
    ⟨S', h_image_subset⟩,
    Set.Nonempty.image _ σ.nonempty⟩, rfl⟩

end AffineBuilding
