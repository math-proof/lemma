/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.IsometryGroups
set_option linter.unusedSectionVars false


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- A building is **thick** if every panel (codim-$1$ face of a chamber) is contained in at
least three distinct chambers. -/
def IsThick (B : LinearMap.BilinForm k V) (n : ℕ)
    (bldg : IsBuilding B n) : Prop :=
  ∀ panel ∈ bldg.complex.simplices,
    ∀ C₀ ∈ bldg.complex.simplices,
      panel ⊆ C₀ → panel.card + 1 = C₀.card →
      ∃ C₁ C₂ C₃ : Finset (Submodule k V),
        C₁ ∈ bldg.complex.simplices ∧ C₂ ∈ bldg.complex.simplices ∧
        C₃ ∈ bldg.complex.simplices ∧
        panel ⊆ C₁ ∧ panel ⊆ C₂ ∧ panel ⊆ C₃ ∧
        C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃


/-- A building is **strongly transitive** under the isometry group if for any two apartments
$A_1, A_2$ and chambers $C_1 \in A_1$, $C_2 \in A_2$ there is an isometry of $(V,B)$ sending
$A_1$ to $A_2$ and $C_1$ to $C_2$. -/
def StronglyTransitive (B : LinearMap.BilinForm k V) (n : ℕ)
    (bldg : IsBuilding B n) : Prop :=
  ∀ (A₁ A₂ : Apartment B n) (C₁ C₂ : Finset (Submodule k V)),
    A₁ ∈ bldg.apartments → A₂ ∈ bldg.apartments →
    C₁ ∈ A₁.simplices → C₂ ∈ A₂.simplices →
    ∃ g : V ≃ₗ[k] V,
      (∀ v₁ v₂, B (g v₁) (g v₂) = B v₁ v₂) ∧
      (Finset.image (Submodule.map g.toLinearMap) C₁ = C₂) ∧
      (∀ σ ∈ A₁.simplices,
        Finset.image (Submodule.map g.toLinearMap) σ ∈ A₂.simplices)


end IsometryBuilding
