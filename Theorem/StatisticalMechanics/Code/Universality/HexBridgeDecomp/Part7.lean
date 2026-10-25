/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part7


namespace StatMech.Universality

open List


@[simp]
theorem hexHW_bridge_decomp_apply (bs : {bs : List HexBridge // StrictDecreasingWidths bs}) :
    (hexHW_bridge_decomp bs : List (ℕ × ℤ)) = bridgeRecompose bs.1 := rfl


theorem hexHW_bridge_decomp_symm_apply (γ : {γ : List (ℕ × ℤ) // hexHW_IsValidWalk γ}) :
    ((hexHW_bridge_decomp.symm γ : {bs : List HexBridge // StrictDecreasingWidths bs}) :
        List HexBridge)
      = bridgeDecomp γ.1 (by
          obtain ⟨bs, _, hrec⟩ := γ.2
          rw [← hrec]; exact hexHW_wf_bridgeRecompose bs) := by
  obtain ⟨bs, hbs, hrec⟩ := γ.2
  have hforward : hexHW_bridge_decomp ⟨bs, hbs⟩ = γ := by
    apply Subtype.ext
    simpa using hrec
  have hsymm : hexHW_bridge_decomp.symm γ = ⟨bs, hbs⟩ := by
    rw [← hforward, Equiv.symm_apply_apply]
  rw [hsymm]
  
  show bs = bridgeDecomp γ.1 _
  have hwf : hexHW_WF γ.1 := by rw [← hrec]; exact hexHW_wf_bridgeRecompose bs
  symm
  calc bridgeDecomp γ.1 hwf
      = bridgeDecomp (bridgeRecompose bs) (hexHW_wf_bridgeRecompose bs) :=
        bridgeDecomp_congr γ.1 (bridgeRecompose bs) hwf (hexHW_wf_bridgeRecompose bs) hrec.symm
    _ = bs := hexHW_decomp_recompose bs _ hbs


theorem hexHW_decomp_strictDecreasing (γ : List (ℕ × ℤ)) (h : hexHW_WF γ)
    (hv : hexHW_IsValidWalk γ) :
    StrictDecreasingWidths (bridgeDecomp γ h) := by
  obtain ⟨bs, hbs, hrec⟩ := hv
  have : bridgeDecomp γ h = bs := by
    rw [bridgeDecomp_congr γ (bridgeRecompose bs) h (hexHW_wf_bridgeRecompose bs) hrec.symm]
    exact hexHW_decomp_recompose bs _ hbs
  rw [this]; exact hbs


theorem hexHW_image_iff (bs : List HexBridge) :
    (∃ (γ : List (ℕ × ℤ)) (h : hexHW_WF γ), hexHW_IsValidWalk γ ∧ bridgeDecomp γ h = bs)
      ↔ StrictDecreasingWidths bs := by
  constructor
  · rintro ⟨γ, h, hv, hd⟩
    rw [← hd]; exact hexHW_decomp_strictDecreasing γ h hv
  · intro hbs
    refine ⟨bridgeRecompose bs, hexHW_wf_bridgeRecompose bs, ⟨bs, hbs, rfl⟩, ?_⟩
    exact hexHW_decomp_recompose bs _ hbs


end StatMech.Universality
