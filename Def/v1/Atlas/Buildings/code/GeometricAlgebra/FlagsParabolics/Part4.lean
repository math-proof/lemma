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
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part3


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

namespace Flag

/-- The parabolic subgroup of `GL(V)` stabilizing a flag `F`: the elements
preserving every space in the flag. -/
def parabolicSubgroup (F : Flag k V) : Subgroup (GLV k V) where
  carrier := { g | ∀ i, (F.spaces i).map (g : V →ₗ[k] V) = F.spaces i }
  mul_mem' := by
    intro a b ha hb; simp only [Set.mem_setOf_eq] at *; intro i
    rw [submodule_map_mul_eq, hb i, ha i]
  one_mem' := by
    simp only [Set.mem_setOf_eq]; intro i; exact Submodule.map_id _
  inv_mem' := by
    intro a ha; simp only [Set.mem_setOf_eq] at *
    intro i; convert map_inv_of_map_to a _ _ (ha i) using 1


/-- The unipotent radical of the parabolic subgroup of `F`: elements in the
parabolic that act as the identity on each successive quotient `F.spaces i /
F.spaces (i-1)` (and as the identity on `F.spaces 0`). -/
def unipotentRadical (F : Flag k V) : Set (GLV k V) :=
  { g | g ∈ F.parabolicSubgroup ∧
    ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      (g : V →ₗ[k] V) v - v ∈
        if h : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩ }


/-- Two flags are opposite if they have the same length and type, and each matched
pair of levels `(F.spaces i, F'.spaces (F'.len - 1 - i))` is complementary. -/
def isOppositeFlag (F F' : Flag k V) : Prop :=
  F.len = F'.len ∧ F.sameType F' ∧
    ∀ (h : F.len = F'.len) (i : Fin F.len),
      let j : Fin F'.len := ⟨F'.len - 1 - i.val, by omega⟩
      F.spaces i ⊔ F'.spaces j = ⊤ ∧ F.spaces i ⊓ F'.spaces j = ⊥

/-- The parabolic subgroup attached to the opposite flag `F'`. -/
def oppositeParabolic (F' : Flag k V) : Subgroup (GLV k V) := F'.parabolicSubgroup

/-- The Levi component associated with an opposite pair of flags `(F, F')`: the
intersection of their parabolic subgroups. -/
def leviComponent (F F' : Flag k V) (_ : isOppositeFlag F F') : Subgroup (GLV k V) :=
  F.parabolicSubgroup ⊓ F'.parabolicSubgroup


/-- The parabolic subgroup of `F` is a semidirect product of its Levi component
(with respect to the opposite flag `F'`) and its unipotent radical: every element
of the parabolic factors uniquely as a Levi times unipotent. -/
def ParabolicsSemidirectProduct (F F' : Flag k V) (h : isOppositeFlag F F') : Prop :=
  (∀ p ∈ F.parabolicSubgroup,
    ∃ m u : GLV k V,
      m ∈ leviComponent F F' h ∧ u ∈ F.unipotentRadical ∧ p = m * u) ∧
  (∀ m₁ m₂ u₁ u₂ : GLV k V,
    m₁ ∈ leviComponent F F' h → m₂ ∈ leviComponent F F' h →
    u₁ ∈ F.unipotentRadical → u₂ ∈ F.unipotentRadical →
    m₁ * u₁ = m₂ * u₂ → m₁ = m₂ ∧ u₁ = u₂)

end Flag


namespace Flag

/-- Drop the top space from a flag, keeping the first `F.len - 1` levels. -/
def truncate (F : Flag k V) (h : 1 ≤ F.len) : Flag k V where
  len := F.len - 1
  spaces := fun i => F.spaces ⟨i.val, by omega⟩
  strictMono := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    exact F.strictMono (show (⟨a, by omega⟩ : Fin F.len) < ⟨b, by omega⟩ from hab)

/-- Drop the bottom space from a flag, keeping levels from index `1` onwards. -/
def truncateStart (F : Flag k V) (h : 1 ≤ F.len) : Flag k V where
  len := F.len - 1
  spaces := fun i => F.spaces ⟨i.val + 1, by omega⟩
  strictMono := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have : a < b := hab
    show F.spaces ⟨a + 1, by omega⟩ < F.spaces ⟨b + 1, by omega⟩
    exact F.strictMono (by simp [Fin.lt_def]; omega)

end Flag
end GeometricAlgebra
