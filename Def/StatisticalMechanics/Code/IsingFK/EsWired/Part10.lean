/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part9
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


def pinnedFunEquiv {α : Type*} [DecidableEq α] {q : ℕ} (c₀ : α) (b : Fin q) :
    {τ : α → Fin q // τ c₀ = b} ≃ ({c : α // c ≠ c₀} → Fin q) where
  toFun τ := fun c => τ.1 c.1
  invFun g := ⟨fun a => if h : a = c₀ then b else g ⟨a, h⟩, by simp⟩
  left_inv := by
    rintro ⟨τ, hτ⟩
    apply Subtype.ext; funext a
    by_cases h : a = c₀
    · simp [h, hτ]
    · simp [h]
  right_inv := by
    intro g; funext c
    obtain ⟨a, ha⟩ := c
    simp [ha]


end IsingFK
end StatMech
