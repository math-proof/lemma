/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AffineSLV.Part4
import Lemma.Set.IsHomothetic_πLattice
import Lemma.Set.ConjSet.eq.Image
import Structure.v1.Atlas.Buildings.code.Building.GroupApplicationsCh17
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Topology.Algebra.Group.Matrix
import Structure.v1.Atlas.Buildings.code.Building.AffineSLVStrong
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace AffineBuildingSLVStrong

open AffineBuildingSLV AffineBuildingSLVAxioms


/-- An $SL_V$-action on the building is strongly transitive with respect to an
apartment system $\mathcal A$ if for any two flagged pairs $(C_1, A_1)$ and
$(C_2, A_2)$ (maximal simplex in an apartment) some $g$ carries the first to the
second. -/
def IsStronglyTransitive (C : DVRContext) (α : SLVAction C)
    (𝒜 : Set (Set (Simplex C))) : Prop :=
  ∀ (C₁ : Simplex C) (A₁ : Set (Simplex C))
    (C₂ : Simplex C) (A₂ : Set (Simplex C)),
    C₁.IsMaximal C → C₂.IsMaximal C →
    A₁ ∈ 𝒜 → A₂ ∈ 𝒜 →
    C₁ ∈ A₁ → C₂ ∈ A₂ →
    ∃ g : SLV C, α.act_simplex g C₁ = C₂ ∧ α.act_apartment g A₁ = A₂

/-- The image of the valuation ring embedding $\mathfrak{o} \hookrightarrow k$ as a
subring of $k$. -/
noncomputable def imageSubring (C : DVRContext) : Subring C.k :=
  C.embed.range

/-- The canonical apartment system: apartments $A_F$ indexed by frames $F$ of $V$.
This is the maximal apartment system for the Bruhat-Tits building of $SL_V$. -/
def frameApartmentSystem (C : DVRContext) : Set (Set (Simplex C)) :=
  {A | ∃ F : Frame C, A = Apartment C F}

/-- A family of apartments is an apartment system if every member arises from a
frame and any two simplices lie together in some apartment of the system. -/
def IsApartmentSystem (C : DVRContext) (sys : Set (Set (Simplex C))) : Prop :=

  (∀ A ∈ sys, ∃ F : Frame C, A = Apartment C F) ∧

  (∀ σ₁ σ₂ : Simplex C, ∃ A ∈ sys, σ₁ ∈ A ∧ σ₂ ∈ A) ∧


  True

/-- An apartment system is maximal if it is an apartment system and contains every
other apartment system. -/
def IsMaximalApartmentSystem (C : DVRContext) (max_apts : Set (Set (Simplex C))) : Prop :=
  IsApartmentSystem C max_apts ∧
  (∀ sys : Set (Set (Simplex C)), IsApartmentSystem C sys → sys ⊆ max_apts)

end AffineBuildingSLVStrong
