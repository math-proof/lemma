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
import Def.v1.Atlas.Buildings.code.BNPair.FromBuilding.Part2
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


/-- **The data needed to build a BN-pair from a strongly transitive action on a building.**
Packages: a `GroupAction` of $G$ on the building $b$, a chosen base apartment $A_0$ with
chamber $C_0$, a bijection $\varphi : \text{chambers of } A_0 \to W$ with $\varphi(C_0) = 1$
that intertwines the $N$-action with left multiplication, and the Bruhat-style hypothesis
$G = B \cdot N \cdot B$. From this data one extracts the strict BN-pair $(B, N, T, \pi)$. -/
structure BNPairFromBuildingData
    {V : Type*} [DecidableEq V]
    (G : Type*) [Group G]
    (b : Building V)
    (ct : Building.CoxeterTypeOfBuilding b) where
  act : Building.GroupAction G b
  A₀ : SimplicialComplex V
  hA₀ : A₀ ∈ b.apartmentSystem.apartments
  C₀ : Finset V
  hC₀_max_A₀ : A₀.IsMaximal C₀
  φ : Finset V → ct.matrix.Group
  φ_inj : ∀ C, A₀.IsMaximal C → ∀ D, A₀.IsMaximal D → φ C = φ D → C = D
  φ_surj : ∀ w : ct.matrix.Group, ∃ C, A₀.IsMaximal C ∧ φ C = w
  φ_base : φ C₀ = 1
  strongly_transitive : act.IsStronglyTransitive
  smul_preserves_apt_max : ∀ (n : G) (_ : act.smulFaces n A₀.faces = A₀.faces)
    (C : Finset V) (_ : A₀.IsMaximal C),
    A₀.IsMaximal (act.smulFace n C)
  φ_equivariant : ∀ (n : G) (_ : act.smulFaces n A₀.faces = A₀.faces)
    (C : Finset V) (_ : A₀.IsMaximal C),
    φ (act.smulFace n C) = φ (act.smulFace n C₀) * φ C
  bruhat_decomp : ∀ g : G, ∃ (b₁ : G) (_ : act.smulFace b₁ C₀ = C₀)
    (n : G) (_ : act.smulFaces n A₀.faces = A₀.faces)
    (b₂ : G) (_ : act.smulFace b₂ C₀ = C₀),
    g = b₁ * n * b₂

