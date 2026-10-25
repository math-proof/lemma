/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerODE
open Complex Set Filter Topology
open scoped NNReal ComplexConjugate


namespace StatMech.SLE

lemma im_loewnerField (W : ℝ → ℝ) (t : ℝ) (w : ℂ) :
    (loewnerField W t w).im = -2 * w.im / Complex.normSq (w - (W t : ℂ)) := by
  rw [loewnerField_apply, Complex.div_im]; simp [Complex.normSq]; ring


lemma im_loewnerField_nonpos {W : ℝ → ℝ} {t : ℝ} {w : ℂ} (hw : 0 ≤ w.im) :
    (loewnerField W t w).im ≤ 0 := by
  rw [im_loewnerField]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (Complex.normSq_nonneg _)


lemma re_loewnerField (W : ℝ → ℝ) (t : ℝ) (w : ℂ) :
    (loewnerField W t w).re =
      2 * (w.re - W t) / Complex.normSq (w - (W t : ℂ)) := by
  rw [loewnerField_apply, Complex.div_re]
  simp [Complex.normSq]


end StatMech.SLE
