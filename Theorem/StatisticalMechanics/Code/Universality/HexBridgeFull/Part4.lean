/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Def.StatisticalMechanics.Code.Universality.HexBridgeFull.Part4


namespace StatMech.Universality

open List

open HexWalk


theorem hxb_walkOf_legalTurns_of_legalRungs (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ))
    (h : hxb_LegalRungs γ) : (hxb_walkOf a h0 γ).LegalTurns := by
  intro t ht
  simp only [hxb_walkOf, hxb_rungTurns, ofTurns_turns, List.mem_map] at ht
  obtain ⟨p, hp, rfl⟩ := ht
  exact h p hp


theorem hxb_legalRungs_recompose (bs : List HexBridge) (h : hxb_LegalContents bs) :
    hxb_LegalRungs (bridgeRecompose bs) := by
  intro p hp
  simp only [bridgeRecompose, List.mem_flatten, List.mem_map] at hp
  obtain ⟨_, ⟨c, hc, rfl⟩, hpc⟩ := hp
  simp only [HexBridge.rungs, List.mem_map] at hpc
  obtain ⟨t, ht, rfl⟩ := hpc
  exact h c hc t ht


theorem hxb_walkOfBridges_legalTurns (a : ℂ) (h0 : ℤ) (bs : List HexBridge)
    (h : hxb_LegalContents bs) : (hxb_walkOfBridges a h0 bs).LegalTurns :=
  hxb_walkOf_legalTurns_of_legalRungs a h0 (bridgeRecompose bs)
    (hxb_legalRungs_recompose bs h)


theorem hxb_walkOfBridges_nil_isLegalSAW (a : ℂ) (h0 : ℤ) :
    (hxb_walkOfBridges a h0 []).IsLegalSAW := by
  rw [hxb_walkOfBridges_nil]
  exact trivialWalk_isLegalSAW a h0


theorem hxb_walkOf_nil_isLegalSAW (a : ℂ) (h0 : ℤ) :
    (hxb_walkOf a h0 []).IsLegalSAW := by
  have : hxb_walkOf a h0 ([] : List (ℕ × ℤ)) = trivialWalk a h0 := by
    unfold hxb_walkOf hxb_rungTurns; simp [trivialWalk, ofTurns]
  rw [this]; exact trivialWalk_isLegalSAW a h0


theorem hxb_walkOf_isLegalSAW_of (a : ℂ) (h0 : ℤ) (bs : List HexBridge)
    (hlegal : hxb_LegalContents bs) (hsaw : (hxb_walkOfBridges a h0 bs).IsSAW) :
    (hxb_walkOfBridges a h0 bs).IsLegalSAW :=
  ⟨hxb_walkOfBridges_legalTurns a h0 bs hlegal, hsaw⟩


theorem hxb_walkOf_bridge_decomp (bs : {bs : List HexBridge // StrictDecreasingWidths bs})
    (a : ℂ) (h0 : ℤ) :
    hxb_walkOf a h0 (hexHW_bridge_decomp bs : List (ℕ × ℤ))
      = hxb_walkOfBridges a h0 bs.1 := by
  rw [hexHW_bridge_decomp_apply]
  rfl


theorem hxb_walkOf_valid_eq_bridges (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ))
    (hv : hexHW_IsValidWalk γ) :
    ∃ bs, StrictDecreasingWidths bs ∧ hxb_walkOf a h0 γ = hxb_walkOfBridges a h0 bs := by
  obtain ⟨bs, hbs, hrec⟩ := hv
  exact ⟨bs, hbs, by rw [hxb_walkOfBridges, hrec]⟩

end StatMech.Universality
