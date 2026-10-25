/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
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

end AffineWeylGroupData
end
