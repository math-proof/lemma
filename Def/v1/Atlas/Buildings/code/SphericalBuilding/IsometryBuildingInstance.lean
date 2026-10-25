/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryBuildingInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryGroups.Part3


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- The standard isotropic flag complex of $(V, B)$: simplices are finite chains
$W_1 \le W_2 \le \cdots$ of totally isotropic subspaces with respect to the bilinear form $B$. -/
noncomputable def standardComplex (B : LinearMap.BilinForm k V) :
    IsotropicFlagComplex B where
  simplices := { σ : Finset (Submodule k V) |
    (∀ W ∈ σ, IsotropicSubspace B W) ∧
    (∀ W₁ ∈ σ, ∀ W₂ ∈ σ, W₁ ≤ W₂ ∨ W₂ ≤ W₁) }
  simplex_isotropic := fun σ hσ W hW => hσ.1 W hW
  simplex_chain := fun σ hσ W₁ hW₁ W₂ hW₂ => hσ.2 W₁ hW₁ W₂ hW₂
  face_closed := fun σ hσ τ hτ_sub hτ_ne => by
    constructor
    · intro W hW; exact hσ.1 W (hτ_sub hW)
    · intro W₁ hW₁ W₂ hW₂; exact hσ.2 W₁ (hτ_sub hW₁) W₂ (hτ_sub hW₂)

/-- The standard apartments of the isometry building, indexed by hyperbolic frames of $(V,B)$ of
rank $n$. Each apartment carries the full set of isotropic chains as its simplices. -/
noncomputable def standardApartments (B : LinearMap.BilinForm k V) (n : ℕ) :
    Set (Apartment B n) :=
  Set.range fun (frame : HyperbolicFrame B n) =>
    { frame := frame
      simplices := { σ : Finset (Submodule k V) |
        (∀ W ∈ σ, IsotropicSubspace B W) ∧
        (∀ W₁ ∈ σ, ∀ W₂ ∈ σ, W₁ ≤ W₂ ∨ W₂ ≤ W₁) } }


end IsometryBuilding
