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
import Class.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Uniqueness in `M ∩ U = {1}`: a linear equivalence that simultaneously preserves
the opposite flag `F'` levelwise and is unipotent along `F` must be the identity. -/
theorem Flag.unipotent_levi_is_id
    (F F' : Flag k V) (hopp : Flag.isOppositeFlag F F')
    (hlen : 0 < F.len) (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (e : V ≃ₗ[k] V)
    (he_F' : ∀ i : Fin F'.len, (F'.spaces i).map e.toLinearMap = F'.spaces i)
    (hunip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      e.toLinearMap v - v ∈
        if _hh : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩) :
    e = LinearEquiv.refl k V := by
  ext v; simp only [LinearEquiv.refl_apply]
  suffices hind : ∀ (n : ℕ) (hn : n < F.len), ∀ w ∈ F.spaces ⟨n, hn⟩, e w = w by
    have hv : v ∈ F.spaces ⟨F.len - 1, by omega⟩ := by rw [hcov]; exact Submodule.mem_top
    exact hind (F.len - 1) (by omega) v hv
  intro n
  induction n with
  | zero =>
    intro hn w hw
    have := hunip ⟨0, hn⟩ w hw; simp at this; rwa [sub_eq_zero] at this
  | succ m ih =>
    intro hn w hw
    have ih_m : ∀ w ∈ F.spaces ⟨m, by omega⟩, e w = w := ih (by omega)
    have hunip_w : e.toLinearMap w - w ∈ F.spaces ⟨m, by omega⟩ := by
      have := hunip ⟨m + 1, hn⟩ w hw; simp at this; exact this
    obtain ⟨hlen_eq, _, hopp_compl⟩ := hopp
    have hopp_m := hopp_compl hlen_eq ⟨m, by omega⟩
    obtain ⟨hsup_m, hinf_m⟩ := hopp_m
    have hw_top : w ∈ F.spaces ⟨m, by omega⟩ ⊔ F'.spaces ⟨F'.len - 1 - m, by omega⟩ := by
      rw [hsup_m]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hw_top
    obtain ⟨wp, hwp, wq, hwq, hwpq⟩ := hw_top
    have hewp : e wp = wp := ih_m wp hwp
    have hew : e w = wp + e wq := by
      rw [← hwpq]; show e (wp + wq) = wp + e wq
      simp [map_add, hewp]
    have h_diff_in_p : e wq - wq ∈ F.spaces ⟨m, by omega⟩ := by
      have hmem : e.toLinearMap w - w ∈ F.spaces ⟨m, by omega⟩ := hunip_w
      have key : e.toLinearMap w - w = e wq - wq := by
        show e w - w = e wq - wq
        rw [hew, ← hwpq]; simp [add_sub_add_left_eq_sub]
      rwa [key] at hmem
    have h_ewq_in_q : e wq ∈ F'.spaces ⟨F'.len - 1 - m, by omega⟩ := by
      rw [← he_F' ⟨F'.len - 1 - m, by omega⟩]; exact Submodule.mem_map_of_mem hwq
    have h_diff_in_q : e wq - wq ∈ F'.spaces ⟨F'.len - 1 - m, by omega⟩ :=
      (F'.spaces ⟨F'.len - 1 - m, by omega⟩).sub_mem h_ewq_in_q hwq
    have h_diff_zero : e wq - wq = 0 := by
      have h4 := Submodule.mem_inf.mpr ⟨h_diff_in_p, h_diff_in_q⟩
      rw [hinf_m, Submodule.mem_bot] at h4; exact h4
    have hewq : e wq = wq := sub_eq_zero.mp h_diff_zero
    rw [hew, hewq, hwpq]

/-- Uniqueness of the Levi-unipotent factorization at the linear-equivalence level:
if `d₁ ∘ u₁ = d₂ ∘ u₂` with both factors lying in the appropriate Levi and
unipotent subspaces, then `d₁ = d₂` and `u₁ = u₂`. -/
theorem Flag.unique_decomp_linear_proof
    (F F' : Flag k V) (hopp : Flag.isOppositeFlag F F')
    (hlen : 0 < F.len) (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (d₁ d₂ u₁ u₂ : V ≃ₗ[k] V)
    (_hd₁_F : ∀ i : Fin F.len, (F.spaces i).map d₁.toLinearMap = F.spaces i)
    (hd₁_F' : ∀ i : Fin F'.len, (F'.spaces i).map d₁.toLinearMap = F'.spaces i)
    (_hd₂_F : ∀ i : Fin F.len, (F.spaces i).map d₂.toLinearMap = F.spaces i)
    (hd₂_F' : ∀ i : Fin F'.len, (F'.spaces i).map d₂.toLinearMap = F'.spaces i)
    (hu₁_F : ∀ i : Fin F.len, (F.spaces i).map u₁.toLinearMap = F.spaces i)
    (hu₁_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      u₁.toLinearMap v - v ∈
        if _hh : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩)
    (_hu₂_F : ∀ i : Fin F.len, (F.spaces i).map u₂.toLinearMap = F.spaces i)
    (hu₂_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      u₂.toLinearMap v - v ∈
        if _hh : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩)
    (hcomp : d₁.toLinearMap.comp u₁.toLinearMap = d₂.toLinearMap.comp u₂.toLinearMap) :
    d₁ = d₂ ∧ u₁ = u₂ := by


  set e := d₁.trans d₂.symm with he_def

  have he_F' : ∀ i : Fin F'.len, (F'.spaces i).map e.toLinearMap = F'.spaces i := by
    intro i
    show (F'.spaces i).map (d₂.symm.toLinearMap.comp d₁.toLinearMap) = F'.spaces i
    rw [Submodule.map_comp, hd₁_F' i, map_inv_of_map_eq d₂ _ (hd₂_F' i)]

  have he_eq : ∀ v : V, e v = u₂ (u₁.symm v) := by
    intro v
    show d₂.symm (d₁ v) = u₂ (u₁.symm v)
    have hc := LinearMap.congr_fun hcomp (u₁.symm v)
    simp at hc
    have := congr_arg d₂.symm hc
    simp at this
    exact this

  have he_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      e.toLinearMap v - v ∈
        if hh : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩ := by
    intro i v hv
    set w := u₁.symm v with hw_def
    have hw_mem : w ∈ F.spaces i := by
      rw [← map_inv_of_map_eq u₁ _ (hu₁_F i)]; exact Submodule.mem_map_of_mem hv
    have hev : e v = u₂ w := he_eq v
    have hew_diff : e v - v = (u₂ w - w) - (u₁ w - w) := by
      rw [hev, hw_def]; simp [LinearEquiv.apply_symm_apply]
    rw [show e.toLinearMap v - v = e v - v from rfl, hew_diff]
    have h1 := hu₂_unip i w hw_mem
    have h2 := hu₁_unip i w hw_mem
    split_ifs at h1 h2 ⊢ with hi
    · rw [Submodule.mem_bot] at h1 h2 ⊢
      rw [show u₂ w = (u₂.toLinearMap w : V) from rfl,
          show u₁ w = (u₁.toLinearMap w : V) from rfl, h1, h2, sub_self]
    · exact (F.spaces ⟨i.val - 1, by omega⟩).sub_mem h1 h2

  have he_id := Flag.unipotent_levi_is_id F F' hopp hlen hcov e he_F' he_unip

  have hd_eq : d₁ = d₂ := by
    ext v
    have h := LinearEquiv.congr_fun he_id v
    simp [he_def] at h
    have := congr_arg d₂ h
    simp at this
    exact this

  have hu_eq : u₁ = u₂ := by
    ext v
    have hc := LinearMap.congr_fun hcomp v
    simp at hc
    rw [hd_eq] at hc
    exact d₂.injective hc
  exact ⟨hd_eq, hu_eq⟩

end GeometricAlgebra
