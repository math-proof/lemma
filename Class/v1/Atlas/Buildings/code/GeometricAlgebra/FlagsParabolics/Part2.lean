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
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part5


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Combined property packaging both existence and uniqueness of the Levi-unipotent
decomposition of the flag stabilizer. -/
class SemidirectDecompositionProperty (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : Prop where
  exists_decomp_linear : ∀ (F F' : Flag k V) (_h : Flag.isOppositeFlag F F')
    (hlen : 0 < F.len) (_hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (p : V ≃ₗ[k] V),
    (∀ i : Fin F.len, (F.spaces i).map p.toLinearMap = F.spaces i) →
      ∃ (d u : V ≃ₗ[k] V),
        (∀ i : Fin F.len, (F.spaces i).map d.toLinearMap = F.spaces i) ∧
        (∀ i : Fin F'.len, (F'.spaces i).map d.toLinearMap = F'.spaces i) ∧
        (∀ i : Fin F.len, (F.spaces i).map u.toLinearMap = F.spaces i) ∧
        (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
          u.toLinearMap v - v ∈
            if _ : (i : ℕ) = 0 then (⊥ : Submodule k V)
            else F.spaces ⟨i.val - 1, by omega⟩) ∧
        p.toLinearMap = d.toLinearMap.comp u.toLinearMap
  unique_decomp_linear : ∀ (F F' : Flag k V) (_h : Flag.isOppositeFlag F F')
    (hlen : 0 < F.len) (_hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (d₁ d₂ u₁ u₂ : V ≃ₗ[k] V),
    (∀ i : Fin F.len, (F.spaces i).map d₁.toLinearMap = F.spaces i) →
    (∀ i : Fin F'.len, (F'.spaces i).map d₁.toLinearMap = F'.spaces i) →
    (∀ i : Fin F.len, (F.spaces i).map d₂.toLinearMap = F.spaces i) →
    (∀ i : Fin F'.len, (F'.spaces i).map d₂.toLinearMap = F'.spaces i) →
    (∀ i : Fin F.len, (F.spaces i).map u₁.toLinearMap = F.spaces i) →
    (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      u₁.toLinearMap v - v ∈
        if _ : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩) →
    (∀ i : Fin F.len, (F.spaces i).map u₂.toLinearMap = F.spaces i) →
    (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      u₂.toLinearMap v - v ∈
        if _ : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩) →
    d₁.toLinearMap.comp u₁.toLinearMap = d₂.toLinearMap.comp u₂.toLinearMap →
    d₁ = d₂ ∧ u₁ = u₂

end GeometricAlgebra
