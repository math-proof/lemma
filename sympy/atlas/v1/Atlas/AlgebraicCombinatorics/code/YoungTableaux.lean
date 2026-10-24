/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungTableaux.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic

noncomputable section

open scoped Classical
open Finset

namespace YoungDiagram

theorem rowLen_eq_zero_of_colLen_le (μ : YoungDiagram) {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  have hpos : 0 < μ.rowLen i := Nat.pos_of_ne_zero h
  have : (i, 0) ∈ μ := mem_iff_lt_rowLen.mpr hpos
  rw [mem_iff_lt_colLen] at this
  omega

lemma rowLen_antitone (μ : YoungDiagram) : Antitone μ.rowLen := by
  intro i j hij
  by_contra hc; push Not at hc
  have h1 : (j, μ.rowLen i) ∈ μ := mem_iff_lt_rowLen.mpr (by omega)
  have h2 : (i, μ.rowLen i) ∈ μ :=
    μ.isLowerSet (Prod.mk_le_mk.mpr ⟨hij, le_rfl⟩) h1
  rw [mem_iff_lt_rowLen] at h2; omega

lemma rowLen_gt_of_lt_addable (μ : YoungDiagram) {i : ℕ}
    (hadd : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i) {c : ℕ} (hc : c < i) :
    μ.rowLen c > μ.rowLen i := by
  rcases hadd with rfl | h
  · omega
  · exact lt_of_lt_of_le h (rowLen_antitone μ (by omega))

def addableRows (μ : YoungDiagram) : Finset ℕ :=
  (Finset.range (μ.colLen 0 + 1)).filter
    (fun i => i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i)

def removableRows (μ : YoungDiagram) : Finset ℕ :=
  (Finset.range (μ.colLen 0)).filter
    (fun i => i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1))

noncomputable def addCell (μ : YoungDiagram) (i : ℕ)
    (hadd : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i) : YoungDiagram :=
  ⟨μ.cells ∪ {(i, μ.rowLen i)}, by
    intro ⟨a, b⟩ ⟨c, d⟩ hle hmem
    simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff,
               Finset.mem_coe] at hmem ⊢
    rcases hmem with h | h
    · left; exact μ.isLowerSet hle (Finset.mem_coe.mpr h)
    · rw [h] at hle; simp only [Prod.le_def] at hle; obtain ⟨hci, hdi⟩ := hle
      by_cases hc_lt : c < i
      · left; exact Finset.mem_coe.mpr (mem_iff_lt_rowLen.mpr
          (lt_of_le_of_lt hdi (rowLen_gt_of_lt_addable μ hadd hc_lt)))
      · by_cases hd_lt : d < μ.rowLen i
        · left; exact Finset.mem_coe.mpr (mem_iff_lt_rowLen.mpr
            (lt_of_lt_of_le hd_lt (rowLen_antitone μ (by omega))))
        · right; exact Prod.mk_inj.mpr ⟨by omega, by omega⟩⟩

noncomputable def removeCell (μ : YoungDiagram) (i : ℕ)
    (hrem : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1)) : YoungDiagram :=
  ⟨μ.cells.erase (i, μ.rowLen i - 1), by
    intro ⟨a, b⟩ ⟨c, d⟩ hle hmem
    simp only [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe] at hmem ⊢
    obtain ⟨hmem_in, hmem_ne⟩ := hmem
    refine ⟨μ.isLowerSet hle (Finset.mem_coe.mpr hmem_in), fun heq => ?_⟩
    rw [heq] at hle; simp only [Prod.le_def] at hle; obtain ⟨hia, hrlb⟩ := hle
    have hmem_mu := (μ.mem_cells (a, b)).mp hmem_in
    rw [mem_iff_lt_rowLen] at hmem_mu
    have ha_eq : a = i := by
      by_contra ha_ne
      have h1 : μ.rowLen a ≤ μ.rowLen (i + 1) := rowLen_antitone μ (by omega)
      rcases hrem with h | h
      · have := rowLen_eq_zero_of_colLen_le μ (by omega : μ.colLen 0 ≤ i + 1); omega
      · omega
    rw [ha_eq] at hmem_mu
    exact hmem_ne (Prod.mk_inj.mpr ⟨ha_eq, by omega⟩)⟩

noncomputable def coversUp (μ : YoungDiagram) : Finset YoungDiagram :=
  μ.addableRows.image (fun i =>
    if h : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i then μ.addCell i h else μ)

noncomputable def coversDown (μ : YoungDiagram) : Finset YoungDiagram :=
  μ.removableRows.image (fun i =>
    if h : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1) then μ.removeCell i h else μ)

noncomputable def raisingOp (lam : YoungDiagram) : YoungDiagram →₀ ℤ :=
  lam.coversUp.sum (fun σ => Finsupp.single σ 1)

noncomputable def loweringOp (lam : YoungDiagram) : YoungDiagram →₀ ℤ :=
  lam.coversDown.sum (fun ν => Finsupp.single ν 1)

noncomputable def DU_apply (lam mu : YoungDiagram) : ℤ :=
  lam.coversUp.sum (fun σ => (loweringOp σ) mu)

noncomputable def UD_apply (lam mu : YoungDiagram) : ℤ :=
  lam.coversDown.sum (fun ν => (raisingOp ν) mu)

noncomputable def DUCoeff (lam mu : YoungDiagram) : ℕ :=
  (lam.coversUp.filter (fun σ => mu ∈ σ.coversDown)).card

noncomputable def UDCoeff (lam mu : YoungDiagram) : ℕ :=
  (lam.coversDown.filter (fun ρ => mu ∈ ρ.coversUp)).card

def DUCoeff_cases (lam mu : YoungDiagram) : ℕ :=
  if lam = mu then lam.addableRows.card
  else if (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1 then 1
  else 0

def UDCoeff_cases (lam mu : YoungDiagram) : ℕ :=
  if lam = mu then lam.removableRows.card
  else if (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1 then 1
  else 0
