/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.Finset.Card
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset.Part2
open Finset MulAction
open scoped Pointwise


namespace SpernerProperty

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

section Order

instance quotientPosetPartialOrder :
    PartialOrder (QuotientPoset n G) where
  le a b := ∃ (S T : Finset (Fin n)),
    Quotient.mk (orbitRel G _) S = a ∧
    Quotient.mk (orbitRel G _) T = b ∧ S ⊆ T
  le_refl a := by
    induction a using Quotient.inductionOn with
    | _ S => exact ⟨S, S, rfl, rfl, Finset.Subset.refl _⟩
  le_trans a b c := by
    rintro ⟨S₁, T₁, hS₁, hT₁, hsub₁⟩ ⟨S₂, T₂, hS₂, hT₂, hsub₂⟩
    have hrel : (orbitRel G (Finset (Fin n))).r T₁ S₂ :=
      Quotient.exact (hT₁.trans hS₂.symm)
    rw [orbitRel_apply] at hrel
    obtain ⟨g, hg_eq⟩ := hrel
    refine ⟨g⁻¹ • S₁, T₂, ?_, hT₂, ?_⟩
    · exact (mk_smul_eq g⁻¹ S₁).trans hS₁
    · calc g⁻¹ • S₁ ⊆ g⁻¹ • T₁ :=
            Finset.smul_finset_subset_smul_finset hsub₁
        _ = S₂ := by rw [← hg_eq, inv_smul_smul]
        _ ⊆ T₂ := hsub₂
  le_antisymm a b := by
    classical
    rintro ⟨S₁, T₁, hS₁, hT₁, hsub₁⟩ ⟨S₂, T₂, hS₂, hT₂, hsub₂⟩
    have hcard_a : S₁.card = T₂.card :=
      card_eq_of_mk_eq (hS₁.trans hT₂.symm)
    have hcard_b : T₁.card = S₂.card :=
      card_eq_of_mk_eq (hT₁.trans hS₂.symm)
    have h_card_eq : S₁.card = T₁.card := by
      have h1 := Finset.card_le_card hsub₁
      have h2 := Finset.card_le_card hsub₂
      omega
    have h_eq : S₁ = T₁ := Finset.eq_of_subset_of_card_le hsub₁ h_card_eq.symm.le
    rw [← hS₁, ← hT₁, h_eq]

end Order

noncomputable instance quotientPosetFintype :
    Fintype (QuotientPoset n G) := by
  classical
  exact Quotient.fintype _

end SpernerProperty
