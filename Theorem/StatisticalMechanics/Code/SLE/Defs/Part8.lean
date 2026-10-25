/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.SLE.Defs.Part7
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

@[simp] lemma sleDriving_apply {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω) (t : ℝ) :
    sleDriving κ B ω t = Real.sqrt κ * B t ω := rfl


end StatMech.SLE
