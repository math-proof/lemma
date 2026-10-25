/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
import Mathlib.GroupTheory.SemidirectProduct
import Abbrev.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Data witnessing that a concrete subgroup of $\mathrm{Isom}(E)$ realizes the affine
Weyl group as a semidirect product: every element decomposes as a linear part plus a
coroot translation, with the linear part in $W$ and the translation in $Λ(\check Φ)$, and
every pair $(w, v) ∈ W × Λ(\check Φ)$ is realized. -/
structure AffineWeylSemidirectData (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] extends AffineWeylGroupFullData E where
  affineWeylSubgroup : Subgroup (E ≃ᵃⁱ[ℝ] E)
  affine_decomp : ∀ g ∈ affineWeylSubgroup, ∀ x : E,
    (g : E ≃ᵃⁱ[ℝ] E) x = (linearPartHom g : E ≃ₗᵢ[ℝ] E) x + (g : E ≃ᵃⁱ[ℝ] E) 0
  translationPart_mem : ∀ g ∈ affineWeylSubgroup,
    (g : E ≃ᵃⁱ[ℝ] E) 0 ∈ corootLattice
  linearPart_mem : ∀ g ∈ affineWeylSubgroup,
    linearPartHom g ∈ weylGroup
  pair_mem : ∀ w ∈ weylGroup, ∀ v ∈ corootLattice,
    ∃ g ∈ affineWeylSubgroup,
      linearPartHom g = (w : E ≃ₗᵢ[ℝ] E) ∧
      (g : E ≃ᵃⁱ[ℝ] E) 0 = v

end
