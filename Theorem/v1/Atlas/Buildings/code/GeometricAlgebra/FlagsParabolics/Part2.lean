/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Group
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part2


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The linear map underlying `glvToLinearEquiv g` is the underlying map of `g`. -/
@[simp] lemma glvToLinearEquiv_toLinearMap (g : GLV k V) :
    (glvToLinearEquiv g).toLinearMap = (↑g : V →ₗ[k] V) := rfl


/-- If a linear equivalence `e` preserves a submodule `W`, then so does its inverse
`e.symm`. -/
theorem map_inv_of_map_eq (e : V ≃ₗ[k] V) (W : Submodule k V)
    (h : W.map e.toLinearMap = W) : W.map e.symm.toLinearMap = W := by
  rw [Submodule.comap_equiv_eq_map_symm e W |>.symm]
  ext v; simp only [Submodule.mem_comap]
  constructor
  · intro hv
    have hmem : e v ∈ W.map e.toLinearMap := by rw [h]; exact hv
    rw [Submodule.mem_map] at hmem; obtain ⟨w, hw, hew⟩ := hmem
    exact e.injective hew ▸ hw
  · intro hv
    have : e v ∈ W.map e.toLinearMap := Submodule.mem_map_of_mem hv
    rwa [h] at this

/-- If `g ∈ GLV k V` sends a submodule `W₁` to `W₂`, then `g⁻¹` sends `W₂` back to `W₁`. -/
theorem map_inv_of_map_to (g : GLV k V) (W₁ W₂ : Submodule k V)
    (h : W₁.map (↑g : V →ₗ[k] V) = W₂) : W₂.map (↑(g⁻¹) : V →ₗ[k] V) = W₁ := by
  rw [← h]; ext x; simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    convert hz using 1; change (↑(g⁻¹ * g) : V →ₗ[k] V) z = z; simp [inv_mul_cancel]
  · intro hx
    exact ⟨(↑g : V →ₗ[k] V) x, ⟨x, hx, rfl⟩,
      by change (↑(g⁻¹ * g) : V →ₗ[k] V) x = x; simp [inv_mul_cancel]⟩


end GeometricAlgebra
