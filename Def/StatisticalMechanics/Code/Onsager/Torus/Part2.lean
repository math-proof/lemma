/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Torus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.StatisticalMechanics.Code.Onsager.Torus


namespace StatMech.Onsager

def onsTorusGraph (L : ℕ) [Fact (2 < L)] : SimpleGraph (ZMod L × ZMod L) where
  Adj := onsTorusAdj L
  symm := by
    constructor
    rintro u v (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩)
    · exact Or.inl ⟨h1.symm, Or.inr (by rw [h2]; ring)⟩
    · exact Or.inl ⟨h1.symm, Or.inl (by rw [h2]; ring)⟩
    · exact Or.inr ⟨h1.symm, Or.inr (by rw [h2]; ring)⟩
    · exact Or.inr ⟨h1.symm, Or.inl (by rw [h2]; ring)⟩
  loopless := by
    have hne1 : (1 : ZMod L) ≠ 0 := by
      have : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
      exact one_ne_zero
    have hnem1 : (-1 : ZMod L) ≠ 0 := neg_ne_zero.mpr hne1
    refine ⟨?_⟩
    rintro v (⟨_, h2 | h2⟩ | ⟨_, h2 | h2⟩)
    · exact hne1 (by linear_combination -h2)
    · exact hnem1 (by linear_combination -h2)
    · exact hne1 (by linear_combination -h2)
    · exact hnem1 (by linear_combination -h2)

end StatMech.Onsager
