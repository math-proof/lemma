/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.SLE.Defs
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

lemma isCompactHull_empty : IsCompactHull (∅ : Set ℂ) where
  subset := Set.empty_subset _
  bounded := Bornology.isBounded_empty
  relClosed := ⟨∅, isClosed_empty, by simp⟩
  complement_open := by simpa using isOpen_upperHalfPlane
  complement_connected := by
    have h : upperHalfPlane = {c : ℂ | (0 : ℝ) < c.im} := rfl
    simp only [Set.diff_empty, h]
    exact (convex_halfSpace_im_gt 0).isConnected ⟨(0 + 1) * Complex.I, by simp⟩


end StatMech.SLE
