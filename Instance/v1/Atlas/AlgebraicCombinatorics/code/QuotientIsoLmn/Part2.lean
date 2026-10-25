/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part5
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WreathOrbits
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part4
set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn


namespace QuotientIsoLmn

variable {m n : ℕ}

instance wreathQuotientPartialOrder : PartialOrder (WreathQuotient m n) where
  le a b := ∃ (S T : Finset (Fin m × Fin n)),
      wreathQuotientMk S = a ∧ wreathQuotientMk T = b ∧ S ⊆ T
  le_refl a := by
    induction a using Quotient.inductionOn with
    | _ S => exact ⟨S, S, rfl, rfl, Finset.Subset.refl _⟩
  le_trans a b c := by
    rintro ⟨S₁, T₁, hS₁, hT₁, hsub₁⟩ ⟨S₂, T₂, hS₂, hT₂, hsub₂⟩
    obtain ⟨g, hg⟩ := (wreathQuotientMk_eq_iff T₁ S₂).mp (hT₁.trans hS₂.symm)
    refine ⟨g.actOnSet S₁, T₂, ?_, hT₂, ?_⟩
    · rw [wreathQuotientMk_actOnSet]; exact hS₁
    · exact (actOnSet_subset_of_subset g hsub₁).trans (hg ▸ Finset.Subset.refl _) |>.trans hsub₂
  le_antisymm a b := by
    rintro ⟨S₁, T₁, hS₁, hT₁, hsub₁⟩ ⟨S₂, T₂, hS₂, hT₂, hsub₂⟩
    have hce : S₁.card = T₂.card :=
      card_eq_of_sameOrbit ((wreathQuotientMk_eq_iff S₁ T₂).mp (hS₁.trans hT₂.symm))
    have : S₁.card = T₁.card := by
      have h1 := Finset.card_le_card hsub₁; have h2 := Finset.card_le_card hsub₂
      have hce2 : T₁.card = S₂.card :=
        card_eq_of_sameOrbit ((wreathQuotientMk_eq_iff T₁ S₂).mp (hT₁.trans hS₂.symm))
      omega
    rw [← hS₁, ← hT₁, Finset.eq_of_subset_of_card_le hsub₁ this.symm.le]

end QuotientIsoLmn
