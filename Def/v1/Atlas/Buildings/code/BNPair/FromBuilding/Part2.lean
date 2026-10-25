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
import Theorem.v1.Atlas.Buildings.code.BNPair.FromBuilding
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


namespace Building

namespace GroupAction

variable {G : Type*} [Group G] {b : Building V} (act : GroupAction G b)

/-- The action is **type-preserving** with respect to a labelling $\lambda : \text{faces} \to L$
if every $g \in G$ sends each face to one with the same label. This is the property that
forces the BN-pair built from the action to have its $\pi$-projection well-defined. -/
def IsTypePreserving {L : Type*} [DecidableEq L]
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L) : Prop :=
  ∀ (g : G) (s : Finset V),
    s ∈ b.toChamberComplex.toSimplicialComplex.faces →
    lab.labelMap (act.smulFace g s) = lab.labelMap s

/-- The action is **strongly transitive**: for any two pairs $(A_1, C_1)$, $(A_2, C_2)$ of
an apartment together with one of its chambers, some $g \in G$ sends $A_1 \to A_2$ and
$C_1 \to C_2$. This is the geometric hypothesis used to build a BN-pair from the action. -/
def IsStronglyTransitive : Prop :=
  ∀ (A₁ A₂ : SimplicialComplex V) (C₁ C₂ : Finset V),
    A₁ ∈ b.apartmentSystem.apartments →
    A₂ ∈ b.apartmentSystem.apartments →
    A₁.IsMaximal C₁ → A₂.IsMaximal C₂ →
    ∃ g : G,
      act.smulFaces g A₁.faces = A₂.faces ∧
      act.smulFace g C₁ = C₂

/-- The **chamber stabilizer** $\mathrm{Stab}_G(C_0) = \{g \in G : g \cdot C_0 = C_0\}$,
the subgroup that fixes the chamber $C_0$ setwise. This will become the Borel subgroup $B$. -/
def chamberStabilizer (C₀ : Finset V) : Subgroup G where
  carrier := { g | act.smulFace g C₀ = C₀ }
  mul_mem' := by
    intro a c ha hc; simp only [Set.mem_setOf_eq] at *
    rw [smulFace_mul, hc, ha]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact smulFace_one act C₀
  inv_mem' := by
    intro a ha; simp only [Set.mem_setOf_eq] at *
    have h1 : act.smulFace a⁻¹ (act.smulFace a C₀) = C₀ := by
      rw [← smulFace_mul]; simp [smulFace_one, inv_mul_cancel]
    rwa [ha] at h1

/-- The **apartment stabilizer** $\mathrm{Stab}_G(A_0)$: the subgroup of $G$ that maps the
apartment $A_0$ to itself setwise. This will become the subgroup $N$ of the BN-pair. -/
def apartmentStabilizer (A₀ : SimplicialComplex V) : Subgroup G where
  carrier := { g | act.smulFaces g A₀.faces = A₀.faces }
  mul_mem' := by
    intro a c ha hc; simp only [Set.mem_setOf_eq] at *
    rw [smulFaces_mul, hc, ha]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact smulFaces_one act A₀.faces
  inv_mem' := by
    intro a ha; simp only [Set.mem_setOf_eq] at *
    have h1 : act.smulFaces a⁻¹ (act.smulFaces a A₀.faces) = A₀.faces := by
      rw [← smulFaces_mul]; simp [smulFaces_one, inv_mul_cancel]
    rwa [ha] at h1

/-- The **torus** $T = \mathrm{Stab}_G(C_0) \cap \mathrm{Stab}_G(A_0)$: the subgroup fixing
both the base chamber and the base apartment. This will become the torus $T = B \cap N$. -/
def torus (C₀ : Finset V) (A₀ : SimplicialComplex V) : Subgroup G :=
  act.chamberStabilizer C₀ ⊓ act.apartmentStabilizer A₀

/-- The **face stabilizer** of an arbitrary face $F$: $\mathrm{Stab}_G(F) = \{g \in G :
g \cdot F = F\}$. Specializes to `chamberStabilizer` when $F$ is a chamber. -/
def faceStabilizer (F : Finset V) : Subgroup G where
  carrier := { g | act.smulFace g F = F }
  mul_mem' := by
    intro a c ha hc; simp only [Set.mem_setOf_eq] at *
    rw [smulFace_mul, hc, ha]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact smulFace_one act F
  inv_mem' := by
    intro a ha; simp only [Set.mem_setOf_eq] at *
    have h1 : act.smulFace a⁻¹ (act.smulFace a F) = F := by
      rw [← smulFace_mul]; simp [smulFace_one, inv_mul_cancel]
    rwa [ha] at h1

/-- The **geometric standard parabolic** $P_{S'}$ as the stabilizer of the subface of $C_0$
spanned by the vertices whose label lies in $S' \subseteq L$. Matches the algebraic
$P_{S'} = BW_{S'}B$ under the BN-pair built from the action. -/
def standardParabolic {L : Type*} [DecidableEq L]
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L)
    (C₀ : Finset V) (S' : Finset L) : Subgroup G :=
  act.faceStabilizer (C₀.filter (fun v => lab.labelMap {v} ⊆ S'))

/-- Predicate: $g$ and $w$ land in the same Bruhat double coset $BwB$ as measured by the
retraction $\rho$ onto the base apartment; specifically, $\rho(g \cdot C_0) = w \cdot C_0$
in the apartment. -/
def bruhatCosetFromRetraction
    (ρ : BuildingRetraction b) (C₀ : Finset V) (g w : G) : Prop :=
  (act.smulFace g C₀).image ρ.map = act.smulFace w C₀

end GroupAction
end Building
