/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


theorem boxCrossingProbabilities_nonempty
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) (n0 : ℕ) :
    (boxCrossingProbabilities μ ρ n0).Nonempty :=
  ⟨_, n0, 0, le_refl _, Or.inl rfl⟩


theorem boxCrossingProbabilities_bddBelow
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) (n0 : ℕ) :
    BddBelow (boxCrossingProbabilities μ ρ n0) := by
  refine ⟨0, ?_⟩
  rintro z ⟨n, τ, hn, rfl | rfl⟩ <;> exact measureReal_nonneg


theorem boxCrossingProbabilities_mem_Icc
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (ρ : ℝ) (n0 : ℕ) {x : ℝ} (hx : x ∈ boxCrossingProbabilities μ ρ n0) :
    x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨n, τ, hn, h⟩ := hx
  rcases h with rfl | rfl <;> exact ⟨measureReal_nonneg, measureReal_le_one⟩


theorem boxCrossingProbabilities_subset
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) {n0 n0' : ℕ} (h : n0 ≤ n0') :
    boxCrossingProbabilities μ ρ n0' ⊆ boxCrossingProbabilities μ ρ n0 := by
  rintro x ⟨n, τ, hn, hcase⟩
  exact ⟨n, τ, le_trans h hn, hcase⟩


theorem boxCrossingInf_mono
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) {n0 n0' : ℕ} (h : n0 ≤ n0') :
    boxCrossingInf μ ρ n0 ≤ boxCrossingInf μ ρ n0' := by
  unfold boxCrossingInf
  refine csInf_le_csInf (boxCrossingProbabilities_bddBelow μ ρ n0)
    (boxCrossingProbabilities_nonempty μ ρ n0') (boxCrossingProbabilities_subset μ ρ h)


theorem bxp_transfer_core
    (μsrc μtgt : Measure (ConfigSpace (Sym2 (Site 2))))
    (ρsrc ρtgt : ℝ) (n0src n0tgt : ℕ) (hρ : 1 < ρsrc)
    (htgt : 0 < boxCrossingInf μtgt ρtgt n0tgt)
    (hcmp : ∀ x ∈ boxCrossingProbabilities μsrc ρsrc n0src,
        ∃ y ∈ boxCrossingProbabilities μtgt ρtgt n0tgt, y ≤ x) :
    BoxCrossingProperty μsrc ρsrc := by
  refine ⟨hρ, n0src, ?_⟩
  unfold boxCrossingInf at htgt ⊢
  have hSne := boxCrossingProbabilities_nonempty μsrc ρsrc n0src
  have hTbdd := boxCrossingProbabilities_bddBelow μtgt ρtgt n0tgt
  refine lt_of_lt_of_le htgt (le_csInf hSne ?_)
  intro x hx
  obtain ⟨y, hyT, hyx⟩ := hcmp x hx
  exact le_trans (csInf_le hTbdd hyT) hyx


end Universality
end StatMech
