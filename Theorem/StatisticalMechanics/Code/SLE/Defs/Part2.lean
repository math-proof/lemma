/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.SLE.Defs.Part2
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

@[simp] lemma mem_closedUpperHalfPlane {z : ℂ} : z ∈ closedUpperHalfPlane ↔ 0 ≤ z.im := Iff.rfl


lemma isClosed_closedUpperHalfPlane : IsClosed closedUpperHalfPlane := by
  simpa only [closedUpperHalfPlane] using (isClosed_le continuous_const Complex.continuous_im)


lemma upperHalfPlane_subset_closed : upperHalfPlane ⊆ closedUpperHalfPlane :=
  fun _ hz => le_of_lt (mem_upperHalfPlane.mp hz)


end StatMech.SLE
