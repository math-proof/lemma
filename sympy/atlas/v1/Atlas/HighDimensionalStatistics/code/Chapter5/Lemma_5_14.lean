/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers

open Finset Real

noncomputable section

namespace SparseVarshamovGilbert

/-- Hamming distance between two binary vectors. -/
def hammingDist {d : ℕ} (ω₁ ω₂ : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω₁ i ≠ ω₂ i).card

/-- `ℓ⁰`-pseudonorm of a binary vector: number of `true` entries. -/
def l0norm {d : ℕ} (ω : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω i = true).card

/-- Type of `k`-sparse binary vectors in `{0,1}^d`. -/
abbrev SparseVec (d k : ℕ) := {f : Fin d → Bool // l0norm f = k}

/-- The "ball" of `k`-sparse vectors at Hamming distance strictly less than `k/2` (integer
division) from `x`. -/
def sparseBall (d k : ℕ) (x : SparseVec d k) : Finset (SparseVec d k) :=
  Finset.univ.filter fun y => hammingDist x.val y.val < k / 2

/-- There are exactly `k` indices `i : Fin d` with `i.val < k` (assuming `k ≤ d`). -/
lemma card_filter_val_lt (d k : ℕ) (hkd : k ≤ d) :
    (Finset.univ.filter (fun i : Fin d => i.val < k)).card = k := by
  rcases Nat.eq_or_lt_of_le hkd with hkd' | hkd'
  · have : (Finset.univ.filter (fun i : Fin d => i.val < k)) = Finset.univ := by
      ext i; simp [hkd']
    rw [this, Finset.card_univ, Fintype.card_fin]; omega
  · convert Fin.card_Iio (⟨k, hkd'⟩ : Fin d) using 1
    congr 1; ext ⟨i, hi⟩; simp [Finset.mem_filter, Finset.mem_Iio, Fin.lt_def]

/-- A canonical `k`-sparse vector: the indicator of `{i : Fin d | i.val < k}`. -/
def mkSparseVec (d k : ℕ) (hkd : k ≤ d) : SparseVec d k :=
  ⟨fun i => decide (i.val < k), by
    simp only [l0norm, decide_eq_true_eq]; exact card_filter_val_lt d k hkd⟩

/-- Variant of `sparseBall` using the ceiling-style radius `(k+1)/2`. -/
def sparseBallCeil (d k : ℕ) (x : SparseVec d k) : Finset (SparseVec d k) :=
  Finset.univ.filter fun y => hammingDist x.val y.val < (k + 1) / 2

/-- Support of a binary vector: the finset of indices `i` with `f i = true`. -/
def supp {d : ℕ} (f : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter fun i => f i = true

/-- The `i`-th standard binary unit vector in `{0,1}^d`. -/
def unitVec (d : ℕ) (i : Fin d) : Fin d → Bool := fun j => i == j

/-- The `ℓ⁰`-norm of `unitVec d i` is `1`. -/
lemma l0norm_unitVec (d : ℕ) (i : Fin d) : l0norm (unitVec d i) = 1 := by
  unfold l0norm unitVec
  simp only [beq_iff_eq]
  have : (Finset.univ.filter fun j : Fin d => i = j) = {i} := by
    ext j; simp [eq_comm]
  rw [this, card_singleton]

/-- The `1`-sparse vector corresponding to coordinate `i`. -/
def sparseVecOfFin (d : ℕ) (i : Fin d) : SparseVec d 1 :=
  ⟨unitVec d i, l0norm_unitVec d i⟩

/-- `|{i : Fin d | a ≤ i.val < a + k}| = k` when `a + k ≤ d`. -/
lemma card_filter_interval (d a k : ℕ) (h : a + k ≤ d) :
    (Finset.univ.filter (fun i : Fin d => a ≤ i.val ∧ i.val < a + k)).card = k := by
  have hmk : ∀ m : Fin k, a + m.val < d := fun ⟨m, hm⟩ => by omega
  let f : Fin k → Fin d := fun m => ⟨a + m.val, hmk m⟩
  have hf_inj : Function.Injective f := by intro x y hab; ext; simp [f] at hab; omega
  have himg : (Finset.univ.filter (fun i : Fin d => a ≤ i.val ∧ i.val < a + k)) =
    (Finset.univ : Finset (Fin k)).image f := by
    ext ⟨i, _⟩; constructor
    · intro hmem; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      simp only [Finset.mem_image, Finset.mem_univ, true_and, f, Fin.ext_iff]
      exact ⟨⟨i - a, by omega⟩, by simp; omega⟩
    · intro hmem; simp only [Finset.mem_image, Finset.mem_univ, true_and, f, Fin.ext_iff] at hmem
      obtain ⟨⟨m, _⟩, hval⟩ := hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp at hval; omega
  rw [himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]

/-- The `j`-th block of `k` consecutive indices, packaged as a `k`-sparse vector. -/
def blockSparseVec (d k : ℕ) (hkd : k ≤ d / 8) (j : Fin 8) : SparseVec d k :=
  ⟨fun i => decide (j.val * k ≤ i.val ∧ i.val < j.val * k + k), by
    simp only [l0norm, decide_eq_true_eq]
    apply card_filter_interval
    have h1 : 8 * k ≤ d := by have := Nat.div_mul_le_self d 8; omega
    nlinarith [j.isLt]⟩
