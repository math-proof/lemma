/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
import Mathlib.GroupTheory.SemidirectProduct

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylGroupData

variable (d : AffineWeylGroupData E)

/-- The additive automorphism of the coroot lattice $Λ(\check Φ)$ induced by an element
$w$ of the linear Weyl group. -/
def weylActionAddAut (w : ↥d.weylGroup) : AddAut ↥d.corootLattice where
  toFun v := ⟨(w : E ≃ₗᵢ[ℝ] E) v, d.weylGroup_stable_corootLattice w w.prop v v.prop⟩
  invFun v := ⟨(w : E ≃ₗᵢ[ℝ] E)⁻¹ v, by
    have : (↑w⁻¹ : E ≃ₗᵢ[ℝ] E) ↑v ∈ d.corootLattice :=
      d.weylGroup_stable_corootLattice w⁻¹ (d.weylGroup.inv_mem w.prop) v v.prop
    convert this using 1⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp
  map_add' a b := by ext; simp [map_add]

/-- The induced homomorphism $W → \mathrm{MulAut}(\mathrm{Multiplicative}\ Λ(\check Φ))$
used to form the semidirect product $W_a = Λ(\check Φ) ⋊ W$. -/
def weylActionMulAutHom :
    ↥d.weylGroup →* MulAut (Multiplicative ↥d.corootLattice) where
  toFun w := AddEquiv.toMultiplicative (d.weylActionAddAut w)
  map_one' := by
    sorry
  map_mul' w₁ w₂ := by
    sorry

/-- The abstract semidirect product $Λ(\check Φ) ⋊ W$ associated to the affine Weyl
group data. -/
abbrev AffineWeylSemidirect :=
  (Multiplicative ↥d.corootLattice) ⋊[d.weylActionMulAutHom] ↥d.weylGroup

end AffineWeylGroupData

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

namespace AffineWeylSemidirectData

variable (d : AffineWeylSemidirectData E)

/-- Shorthand for the abstract semidirect product type. -/
abbrev SemiType := d.toAffineWeylGroupData.AffineWeylSemidirect

/-- Map sending $g ∈ W_a$ to the pair $(g\cdot 0,\ \mathrm{linearPart}(g))$ in the
semidirect product. -/
def toSemidirect (g : ↥d.affineWeylSubgroup) : d.SemiType :=
  ⟨Multiplicative.ofAdd ⟨(g : E ≃ᵃⁱ[ℝ] E) 0, d.translationPart_mem g g.prop⟩,
   ⟨linearPartHom (g : E ≃ᵃⁱ[ℝ] E), d.linearPart_mem g g.prop⟩⟩

theorem toSemidirect_surjective : Function.Surjective d.toSemidirect := by
  sorry

theorem toSemidirect_injective : Function.Injective d.toSemidirect := by
  sorry

theorem toSemidirect_mul (x y : d.affineWeylSubgroup) :
    d.toSemidirect (x * y) = d.toSemidirect x * d.toSemidirect y := by
  sorry

/-- The promised group isomorphism $W_a ≃ Λ(\check Φ) ⋊ W$. -/
def affineWeyl_semidirect_equiv : ↥d.affineWeylSubgroup ≃* d.SemiType where
  toFun := d.toSemidirect
  invFun := Function.surjInv d.toSemidirect_surjective
  left_inv _ := d.toSemidirect_injective (Function.surjInv_eq d.toSemidirect_surjective _)
  right_inv s := Function.surjInv_eq d.toSemidirect_surjective s
  map_mul' := d.toSemidirect_mul

end AffineWeylSemidirectData

namespace AffineWeylGroup

variable (Wa : AffineWeylGroup E)

/-- The set of affine reflections of the affine Weyl group $W_a$. -/
def affineReflections : Set (E ≃ᵃⁱ[ℝ] E) :=
  {s | s ∈ Wa.reflGroup.group ∧
    ∃ η ∈ Wa.reflGroup.arrangement.hyperplanes,
      (∀ y ∈ η.carrier, s y = y) ∧ s * s = 1}
