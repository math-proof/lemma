/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import Def.StatisticalMechanics.Code.SLE.Defs
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology

public section

namespace StatMech.SLE

@[simp] lemma mem_upperHalfPlane {z : ℂ} : z ∈ upperHalfPlane ↔ 0 < z.im := Iff.rfl


lemma isOpen_upperHalfPlane : IsOpen upperHalfPlane := by
  simpa only [upperHalfPlane] using (isOpen_lt continuous_const Complex.continuous_im)


end StatMech.SLE
