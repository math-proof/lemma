/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryBuildingInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryGroups.Part3
import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryBuildingInstance


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- Hypothesis: for any two isotropic simplices $\sigma_1, \sigma_2$ in the standard complex,
there exists a standard apartment containing both. -/
structure CommonIsotropicApartmentHyp (B : LinearMap.BilinForm k V) (n : ℕ) where
  find_common : ∀ σ₁ ∈ (standardComplex B).simplices, ∀ σ₂ ∈ (standardComplex B).simplices,
    ∃ A ∈ standardApartments B n, σ₁ ∈ A.simplices ∧ σ₂ ∈ A.simplices

/-- Hypothesis: whenever two apartments $A_1, A_2$ share a chamber $C$, there is a bijection
$f : A_1 \to A_2$ of their simplices fixing every simplex in $A_1 \cap A_2$. -/
structure ApartmentExchangeHyp (B : LinearMap.BilinForm k V) (n : ℕ) where
  exchange : ∀ A₁ ∈ standardApartments B n, ∀ A₂ ∈ standardApartments B n,
    ∀ C ∈ A₁.simplices, C ∈ A₂.simplices →
    ∃ f : Finset (Submodule k V) → Finset (Submodule k V),
      Function.Bijective f ∧
      (∀ σ ∈ A₁.simplices, f σ ∈ A₂.simplices) ∧
      (∀ σ ∈ A₁.simplices ∩ A₂.simplices, f σ = σ)


end IsometryBuilding
