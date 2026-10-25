/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.SLE.Defs.Part3
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

@[simp] lemma mem_realLine {z : ℂ} : z ∈ realLine ↔ z.im = 0 := Iff.rfl


lemma ofReal_mem_realLine (x : ℝ) : (x : ℂ) ∈ realLine := by simp [realLine]


end StatMech.SLE
