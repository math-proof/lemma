/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Lemma.Finset.IsMaximalToSimplicialComplex.of.IsMaximal.In_Apartments
import Def.v1.Atlas.Buildings.code.Building.Labels
import Def.v1.Atlas.Buildings.code.Building.RetractionDef
import Structure.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
import Def.v1.Atlas.Buildings.code.BNPair.FromBuilding
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


namespace Building

namespace GroupAction

variable {G : Type*} [Group G] {b : Building V} (act : GroupAction G b)

/-- Compatibility with multiplication: $(g_1 g_2) \cdot s = g_1 \cdot (g_2 \cdot s)$ on faces. -/
theorem smulFace_mul (g₁ g₂ : G) (s : Finset V) :
    act.smulFace (g₁ * g₂) s = act.smulFace g₁ (act.smulFace g₂ s) := by
  simp only [smulFace]
  ext v; simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hv⟩
    exact ⟨act.smul g₂ w, ⟨w, hw, rfl⟩, by rw [← act.smul_mul]; exact hv⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, hv⟩
    exact ⟨u, hu, by rw [act.smul_mul]; exact hv⟩

/-- Identity acts trivially on faces: $1 \cdot s = s$. -/
theorem smulFace_one (s : Finset V) :
    act.smulFace 1 s = s := by
  simp only [smulFace]
  ext v; simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hv⟩; rw [act.smul_one] at hv; rw [← hv]; exact hw
  · intro hv; exact ⟨v, hv, act.smul_one v⟩

/-- Compatibility with multiplication on sets of faces: $(g_1 g_2) \cdot F = g_1 \cdot (g_2 \cdot F)$. -/
theorem smulFaces_mul (g₁ g₂ : G) (F : Set (Finset V)) :
    act.smulFaces (g₁ * g₂) F = act.smulFaces g₁ (act.smulFaces g₂ F) := by
  ext s; simp only [smulFaces, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨act.smulFace g₂ t, ⟨t, ht, rfl⟩, smulFace_mul act g₁ g₂ t⟩
  · rintro ⟨u, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, (smulFace_mul act g₁ g₂ t).symm⟩

/-- Identity acts trivially on sets of faces: $1 \cdot F = F$. -/
theorem smulFaces_one (F : Set (Finset V)) :
    act.smulFaces 1 F = F := by
  ext s; simp only [smulFaces, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, rfl⟩; rwa [smulFace_one]
  · intro hs; exact ⟨s, hs, (smulFace_one act s).symm⟩

end GroupAction
end Building
