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
import Instance.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Two flags of the same type are linearly equivalent: there exists a linear
automorphism of `V` mapping one to the other levelwise. -/
class FlagEquivalenceProperty (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : Prop where
  equiv_linear : ∀ F₁ F₂ : Flag k V, F₁.sameType F₂ →
    ∃ (e : V ≃ₗ[k] V) (hlen : F₁.len = F₂.len),
      ∀ i : Fin F₁.len, (F₁.spaces i).map e.toLinearMap = F₂.spaces (i.cast hlen)

/-- For any flag `F`, any two flags opposite to `F` are conjugate via a linear
automorphism that preserves `F` levelwise. -/
class OppositeSystemsConjugacyProperty (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : Prop where
  conjugate_linear : ∀ (F : Flag k V) (F'₁ F'₂ : Flag k V)
    (_h₁ : Flag.isOppositeFlag F F'₁) (_h₂ : Flag.isOppositeFlag F F'₂),
    ∃ (e : V ≃ₗ[k] V) (hlen : F'₁.len = F'₂.len),
      (∀ i : Fin F.len, (F.spaces i).map e.toLinearMap = F.spaces i) ∧
      (∀ i : Fin F'₁.len, (F'₁.spaces i).map e.toLinearMap = F'₂.spaces (i.cast hlen))

/-- Any two same-type pairs of opposite flags `(F₁, F'₁)` and `(F₂, F'₂)` are
linearly equivalent: one linear automorphism of `V` carries both `F₁ ↦ F₂` and
`F'₁ ↦ F'₂` levelwise. -/
class CompleteFlagPairEquivalenceProperty (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : Prop where
  equiv_linear : ∀ (F₁ F₂ : Flag k V) (F'₁ F'₂ : Flag k V)
    (_ : Flag.isOppositeFlag F₁ F'₁) (_ : Flag.isOppositeFlag F₂ F'₂),
    F₁.sameType F₂ →
    ∃ (e : V ≃ₗ[k] V) (hlen : F₁.len = F₂.len) (hlen' : F'₁.len = F'₂.len),
      (∀ i : Fin F₁.len, (F₁.spaces i).map e.toLinearMap = F₂.spaces (i.cast hlen)) ∧
      (∀ i : Fin F'₁.len, (F'₁.spaces i).map e.toLinearMap = F'₂.spaces (i.cast hlen'))

end GeometricAlgebra
