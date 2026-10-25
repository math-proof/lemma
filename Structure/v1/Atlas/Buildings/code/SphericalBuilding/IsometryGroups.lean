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
import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryGroups
set_option linter.unusedSectionVars false


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- An **isotropic flag** for $B$: a strictly increasing chain
$W_1 \subsetneq W_2 \subsetneq \cdots \subsetneq W_{\text{len}}$ of totally isotropic subspaces. -/
structure IsotropicFlag (B : LinearMap.BilinForm k V) where
  len : ℕ
  chain : Fin len → Submodule k V
  chain_strictMono : StrictMono chain
  chain_isotropic : ∀ i, IsotropicSubspace B (chain i)


/-- An **isotropic flag complex**: an abstract simplicial complex whose simplices are finite
chains of totally isotropic subspaces of $(V, B)$, closed under nonempty subsets. -/
structure IsotropicFlagComplex (B : LinearMap.BilinForm k V) where
  simplices : Set (Finset (Submodule k V))
  simplex_isotropic : ∀ σ ∈ simplices, ∀ W ∈ σ, IsotropicSubspace B W
  simplex_chain : ∀ σ ∈ simplices, ∀ W₁ ∈ σ, ∀ W₂ ∈ σ, W₁ ≤ W₂ ∨ W₂ ≤ W₁
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (Submodule k V),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices


/-- A **hyperbolic pair** $(e, e')$ for $B$: two isotropic vectors with $B(e, e') = 1$,
spanning a hyperbolic plane. -/
structure HyperbolicPair (B : LinearMap.BilinForm k V) where
  e  : V
  e' : V
  pairing      : B e e' = 1
  e_isotropic  : B e e = 0
  e'_isotropic : B e' e' = 0

/-- A **hyperbolic frame** of rank $n$ for $B$: $n$ pairwise-orthogonal hyperbolic pairs
$\{(e_i, e_i')\}_{i < n}$ giving a Witt decomposition of an isotropic-rich subspace. -/
structure HyperbolicFrame (B : LinearMap.BilinForm k V) (n : ℕ) where
  pairs : Fin n → HyperbolicPair B
  orthogonal_ee : ∀ i j, i ≠ j → B (pairs i).e (pairs j).e = 0
  orthogonal_ee' : ∀ i j, i ≠ j → B (pairs i).e (pairs j).e' = 0
  orthogonal_e'e' : ∀ i j, i ≠ j → B (pairs i).e' (pairs j).e' = 0


/-- An **apartment** of rank $n$ in the isometry building: a hyperbolic frame together with
the set of simplices it carries. -/
structure Apartment (B : LinearMap.BilinForm k V) (n : ℕ) where
  frame : HyperbolicFrame B n
  simplices : Set (Finset (Submodule k V))


/-- The data of a **building** structure on the isotropic flag complex of $(V,B)$: a family of
apartments satisfying the common-apartment and apartment-exchange axioms (B1 and B2). -/
structure IsBuilding (B : LinearMap.BilinForm k V) (n : ℕ) where
  complex : IsotropicFlagComplex B
  apartments : Set (Apartment B n)
  apartment_subcomplex : ∀ A ∈ apartments, A.simplices ⊆ complex.simplices
  common_apartment : ∀ σ₁ ∈ complex.simplices, ∀ σ₂ ∈ complex.simplices,
    ∃ A ∈ apartments, σ₁ ∈ A.simplices ∧ σ₂ ∈ A.simplices
  apartment_exchange : ∀ A₁ ∈ apartments, ∀ A₂ ∈ apartments,
    ∀ C ∈ A₁.simplices, C ∈ A₂.simplices →
    ∃ f : Finset (Submodule k V) → Finset (Submodule k V),
      Function.Bijective f ∧
      (∀ σ ∈ A₁.simplices, f σ ∈ A₂.simplices) ∧
      (∀ σ ∈ A₁.simplices ∩ A₂.simplices, f σ = σ)


end IsometryBuilding
