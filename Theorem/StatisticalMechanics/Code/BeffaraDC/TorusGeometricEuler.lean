/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.BeffaraDC.TorusGeometricEuler
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice (card_components_bot card_components_eq_one_of_connected)

open StatMech.Onsager


@[simp] theorem torusQuarterTurn_apply (L : ℕ) (v : ZMod L × ZMod L) :
    torusQuarterTurn L v = (v.2, -v.1) := rfl


theorem torusQuarterTurn_adj_iff (L : ℕ) [Fact (2 < L)]
    (u v : ZMod L × ZMod L) :
    (onsTorusGraph L).Adj (torusQuarterTurn L u) (torusQuarterTurn L v) ↔
      (onsTorusGraph L).Adj u v := by
  simp only [onsTorusGraph, onsTorusAdj, torusQuarterTurn_apply]
  constructor
  · rintro (⟨h, h' | h'⟩ | ⟨h, h' | h'⟩)
    · exact Or.inr ⟨h, Or.inr (by linear_combination -h')⟩
    · exact Or.inr ⟨h, Or.inl (by linear_combination -h')⟩
    · exact Or.inl ⟨by linear_combination -h, Or.inl h'⟩
    · exact Or.inl ⟨by linear_combination -h, Or.inr h'⟩
  · rintro (⟨h, h' | h'⟩ | ⟨h, h' | h'⟩)
    · exact Or.inr ⟨by linear_combination -h, Or.inl h'⟩
    · exact Or.inr ⟨by linear_combination -h, Or.inr h'⟩
    · exact Or.inl ⟨h, Or.inr (by linear_combination -h')⟩
    · exact Or.inl ⟨h, Or.inl (by linear_combination -h')⟩


end StatMech.BeffaraDC
