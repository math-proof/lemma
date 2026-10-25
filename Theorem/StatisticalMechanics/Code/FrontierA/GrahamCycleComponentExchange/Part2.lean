/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCycleComponentExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.FrontierA.GrahamCycleComponentExchange.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

theorem cyclePairComponentExchange_card_le
    (ends : I → Sym2 W) (K L : Finset I) (u v : W)
    (hKL : Disjoint K L) :
    Fintype.card (boundarySector ends K ∅ × boundarySector ends L ∅) ≤
      Fintype.card
        (boundarySector ends
            ((K \ edgeComponent ends K u) ∪ edgeComponent ends L v) ∅ ×
          boundarySector ends
            ((L \ edgeComponent ends L v) ∪ edgeComponent ends K u) ∅) := by
  exact Fintype.card_le_of_embedding
    (cyclePairComponentExchangeEmbedding ends K L u v hKL)


theorem cycleSpaceWeight_componentExchange_le
    (ends : I → Sym2 W) (K L : Finset I) (u v : W)
    (hKL : Disjoint K L) :
    Fintype.card (boundarySector ends K ∅) *
        Fintype.card (boundarySector ends L ∅) ≤
      Fintype.card
          (boundarySector ends
            ((K \ edgeComponent ends K u) ∪ edgeComponent ends L v) ∅) *
        Fintype.card
          (boundarySector ends
            ((L \ edgeComponent ends L v) ∪ edgeComponent ends K u) ∅) := by
  simpa only [Fintype.card_prod] using
    cyclePairComponentExchange_card_le ends K L u v hKL


theorem rowSupportWeight_le_componentExchange
    (ends : I → Sym2 W) (m K : Finset I) (k zero : W)
    (hKm : K ⊆ m) :
    rowSupportWeight ends m K ≤
      rowSupportWeight ends m
        (exchangeFirstRow ends K (m \ K) k zero) := by
  classical
  let L := m \ K
  let K' := exchangeFirstRow ends K L k zero
  let L' := exchangeSecondRow ends K L k zero
  have hKL : Disjoint K L := by
    rw [Finset.disjoint_left]
    intro i hiK hiL
    exact (Finset.mem_sdiff.mp hiL).2 hiK
  have hE0sub : edgeComponent ends K zero ⊆ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hE1sub : edgeComponent ends L k ⊆ L := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hcompl : m \ K' = L' := by
    ext i
    have hE0 := @hE0sub i
    have hE1 := @hE1sub i
    have hKi := @hKm i
    simp only [K', L', exchangeFirstRow, exchangeSecondRow,
      Finset.mem_sdiff, Finset.mem_union]
    dsimp only [L] at hE1 ⊢
    by_cases hiK : i ∈ K <;> by_cases him : i ∈ m <;>
      by_cases hiE0 : i ∈ edgeComponent ends K zero <;>
        by_cases hiE1 : i ∈ edgeComponent ends (m \ K) k <;>
          simp [hiK, him, hiE0, hiE1] at hE0 hE1 hKi ⊢
  have hweight :=
    cycleSpaceWeight_componentExchange_le ends K L zero k hKL
  unfold rowSupportWeight
  dsimp only [K', L', L] at hcompl hweight ⊢
  rw [hcompl]
  exact hweight


theorem componentExchange_eq_of_eq_support_and_components
    (ends : I → Sym2 W) (m : Finset I) (k zero : W)
    {K₁ K₂ : Finset I}
    (hsupport :
      exchangeFirstRow ends K₁ (m \ K₁) k zero =
        exchangeFirstRow ends K₂ (m \ K₂) k zero)
    (hzero : edgeComponent ends K₁ zero = edgeComponent ends K₂ zero)
    (hk : edgeComponent ends (m \ K₁) k =
      edgeComponent ends (m \ K₂) k) :
    K₁ = K₂ := by
  classical
  have hA₁ : edgeComponent ends K₁ zero ⊆ K₁ := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hA₂ : edgeComponent ends K₂ zero ⊆ K₂ := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hB₁ : edgeComponent ends (m \ K₁) k ⊆ m \ K₁ := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hB₂ : edgeComponent ends (m \ K₂) k ⊆ m \ K₂ := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hrecover₁ : K₁ =
      (exchangeFirstRow ends K₁ (m \ K₁) k zero \
          edgeComponent ends (m \ K₁) k) ∪
        edgeComponent ends K₁ zero := by
    ext i
    simp only [exchangeFirstRow, Finset.mem_union,
      Finset.mem_sdiff]
    constructor
    · intro hiK
      by_cases hiA : i ∈ edgeComponent ends K₁ zero
      · exact Or.inr hiA
      · refine Or.inl ⟨Or.inl ⟨hiK, hiA⟩, ?_⟩
        intro hiB
        exact (Finset.mem_sdiff.mp (hB₁ hiB)).2 hiK
    · rintro (⟨hiR, hiB⟩ | hiA)
      · rcases hiR with hiK | hiB'
        · exact hiK.1
        · exact False.elim (hiB hiB')
      · exact hA₁ hiA
  have hrecover₂ : K₂ =
      (exchangeFirstRow ends K₂ (m \ K₂) k zero \
          edgeComponent ends (m \ K₂) k) ∪
        edgeComponent ends K₂ zero := by
    ext i
    simp only [exchangeFirstRow, Finset.mem_union,
      Finset.mem_sdiff]
    constructor
    · intro hiK
      by_cases hiA : i ∈ edgeComponent ends K₂ zero
      · exact Or.inr hiA
      · refine Or.inl ⟨Or.inl ⟨hiK, hiA⟩, ?_⟩
        intro hiB
        exact (Finset.mem_sdiff.mp (hB₂ hiB)).2 hiK
    · rintro (⟨hiR, hiB⟩ | hiA)
      · rcases hiR with hiK | hiB'
        · exact hiK.1
        · exact False.elim (hiB hiB')
      · exact hA₂ hiA
  rw [hrecover₁, hrecover₂]
  rw [hsupport, hzero, hk]

end StatMech.GrahamGHS.FourColor
