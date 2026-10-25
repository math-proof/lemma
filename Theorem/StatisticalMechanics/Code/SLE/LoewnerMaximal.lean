/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem positiveOn_Icc_of_deriv_nonneg_while_pos
    {T : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc (0 : ℝ) T)) (hzero : 0 < f 0)
    (hderiv : ∀ s ∈ Ioo (0 : ℝ) T, 0 < f s →
      ∃ v : ℝ, HasDerivAt f v s ∧ 0 ≤ v) :
    ∀ s ∈ Icc (0 : ℝ) T, 0 < f s := by
  intro s hs
  by_contra hnot
  have hfs : f s ≤ 0 := le_of_not_gt hnot
  have hspos : 0 < s := by
    rcases hs.1.eq_or_lt with rfl | hspos
    · exact False.elim ((not_lt_of_ge hfs) hzero)
    · exact hspos
  have hcontS : ContinuousOn f (Icc (0 : ℝ) s) :=
    hcont.mono (Icc_subset_Icc_right hs.2)
  have hzeroMem : (0 : ℝ) ∈ Icc (f s) (f 0) := ⟨hfs, hzero.le⟩
  obtain ⟨r, hr, hre⟩ := intermediate_value_Icc' hspos.le hcontS hzeroMem
  let Z : Set ℝ := {q | q ∈ Icc (0 : ℝ) s ∧ f q = 0}
  have hZclosed : IsClosed Z := by
    dsimp [Z]
    exact isClosed_Icc.isClosed_eq hcontS continuousOn_const
  have hZcompact : IsCompact Z :=
    IsCompact.of_isClosed_subset isCompact_Icc hZclosed (fun _ hq ↦ hq.1)
  have hZnonempty : Z.Nonempty := ⟨r, hr, hre⟩
  obtain ⟨r₀, hr₀Z, hr₀min⟩ :=
    hZcompact.exists_isMinOn hZnonempty continuousOn_id
  have hr₀pos : 0 < r₀ := by
    have hr₀nonneg : 0 ≤ r₀ := hr₀Z.1.1
    rcases hr₀nonneg.eq_or_lt with hr₀zero | hr₀pos
    · rw [← hr₀zero] at hr₀Z
      exact False.elim (hzero.ne' hr₀Z.2)
    · exact hr₀pos
  have hposBefore : ∀ q ∈ Ioo (0 : ℝ) r₀, 0 < f q := by
    intro q hq
    by_contra hqnot
    have hfq : f q ≤ 0 := le_of_not_gt hqnot
    have hcontQ : ContinuousOn f (Icc (0 : ℝ) q) :=
      hcont.mono (Icc_subset_Icc_right
        (hq.2.le.trans (hr₀Z.1.2.trans hs.2)))
    have hmem : (0 : ℝ) ∈ Icc (f q) (f 0) := ⟨hfq, hzero.le⟩
    obtain ⟨p, hp, hpe⟩ := intermediate_value_Icc' hq.1.le hcontQ hmem
    have hpZ : p ∈ Z :=
      ⟨⟨hp.1, hp.2.trans (hq.2.le.trans hr₀Z.1.2)⟩, hpe⟩
    exact (not_lt_of_ge (hr₀min hpZ)) (hp.2.trans_lt hq.2)
  have hmono : MonotoneOn f (Icc (0 : ℝ) r₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r₀)
      (hcont.mono (Icc_subset_Icc_right (hr₀Z.1.2.trans hs.2)))
    · rw [interior_Icc]
      intro q hq
      exact (hderiv q ⟨hq.1, hq.2.trans_le (hr₀Z.1.2.trans hs.2)⟩
        (hposBefore q hq)).choose_spec.1.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro q hq
      obtain ⟨v, hv, hvnonneg⟩ :=
        hderiv q ⟨hq.1, hq.2.trans_le (hr₀Z.1.2.trans hs.2)⟩
          (hposBefore q hq)
      rw [hv.deriv]
      exact hvnonneg
  have := hmono ⟨le_rfl, hr₀pos.le⟩ ⟨hr₀pos.le, le_rfl⟩ hr₀Z.1.1
  rw [hr₀Z.2] at this
  linarith


end StatMech.SLE
