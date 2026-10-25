/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Percolation.DecoupledForestCount.Part3


namespace StatMech.Percolation

open Set SimpleGraph Finset

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


open Classical in

theorem dfc_canonTcount_le_boundary_succ_of_canonBoxOpenForestSucc
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : dfc_CanonBoxOpenForestSucc ω n) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
  classical
  obtain ⟨Vset, hVne, F, _, vx, b, hπ, hacyc, hmin, htriData, hleaf⟩ := h
  set Cf : Finset (Site d) := (boxFinsetBK d n).filter (fun x => IsCanonicalTrifurcation d ω x)
    with hCf
  have hmemCf : ∀ x, x ∈ Cf ↔ x ∈ box d n ∧ IsCanonicalTrifurcation d ω x := by
    intro x; rw [hCf, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]
  have hCfcard : Cf.card = ctc2_canonTcount d ω n := rfl
  have hdeg3 : ∀ x, x ∈ box d n → IsCanonicalTrifurcation d ω x → 3 ≤ F.degree (vx x) := by
    intro x hxbox htri
    obtain ⟨hvx, hreach, hcut⟩ := htriData x hxbox htri
    exact bst_deg_ge_three_of_boxOpenForest hπ hxbox (ctc2_isTrifurcation_of_canonical htri) hvx
      hreach hcut
  have hvxinjOn : Set.InjOn vx Cf := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hmemCf] at hx hy
    have hx' : (vx x : Site d) = x := (htriData x hx.1 hx.2).1
    have hy' : (vx y : Site d) = y := (htriData y hy.1 hy.2).1
    rw [← hx', ← hy', hxy]
  set Cw : Finset (↑Vset : Type) := Cf.image vx with hCw
  have hcardCw : Cw.card = Cf.card := by rw [hCw, Finset.card_image_of_injOn hvxinjOn]
  have hCwdeg : ∀ w ∈ Cw, 3 ≤ F.degree w := by
    intro w hw
    rw [hCw, Finset.mem_image] at hw
    obtain ⟨x, hxC, rfl⟩ := hw
    rw [hmemCf] at hxC
    exact hdeg3 x hxC.1 hxC.2
  have h1 : Cf.card ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := by
    rw [← hcardCw]; exact flc2_trifImage_card_le_deg3 F Cw hCwdeg
  have h2 : (univ.filter (fun v => 3 ≤ F.degree v)).card
      ≤ (univ.filter (fun v => F.degree v = 1)).card :=
    flc2_forest_internal_le_leaves F hacyc hmin
  have h3 : (univ.filter (fun v => F.degree v = 1)).card ≤ boxSV_boundaryCard d (n + 1) := by
    rw [← tfc_boundaryFinset_card]
    apply Finset.card_le_card_of_injOn (fun v : (↑Vset : Type) => (v : Site d))
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, tfc_mem_boundaryFinset]
      exact hleaf v hv.2
    · intro u _ v _ huv; exact Subtype.val_injective huv
  calc ctc2_canonTcount d ω n = Cf.card := hCfcard.symm
    _ ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := h1
    _ ≤ (univ.filter (fun v => F.degree v = 1)).card := h2
    _ ≤ boxSV_boundaryCard d (n + 1) := h3


end StatMech.Percolation
