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
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


namespace Building

/-- A **group action on a building**: a group $G$ acting on the vertex set $V$ that respects
the simplicial structure (faces map to faces) and the apartment system (apartments map to
apartments), plus the usual group action axioms. This packages the geometric "type II" action
of a group on a building used to build a BN-pair from a strongly transitive action. -/
structure GroupAction (G : Type*) [Group G] (b : Building V) where
  smul : G → V → V
  smul_one : ∀ v, smul 1 v = v
  smul_mul : ∀ (g₁ g₂ : G) (v : V), smul (g₁ * g₂) v = smul g₁ (smul g₂ v)
  smul_face : ∀ (g : G) (s : Finset V),
    s ∈ b.toChamberComplex.toSimplicialComplex.faces →
    s.image (smul g) ∈ b.toChamberComplex.toSimplicialComplex.faces
  smul_apartment : ∀ (g : G) (A : SimplicialComplex V),
    A ∈ b.apartmentSystem.apartments →
    ∃ A' ∈ b.apartmentSystem.apartments,
      A'.faces = { s | ∃ t ∈ A.faces, s = t.image (smul g) }

end Building
