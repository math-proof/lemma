/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.SLE.Defs.Part4
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

lemma sleDriving_zero {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω) :
    sleDriving κ B ω 0 = Real.sqrt κ * B 0 ω := rfl


lemma sleDriving_kappa_zero {Ω : Type*} (B : ℝ → Ω → ℝ) (ω : Ω) (t : ℝ) :
    sleDriving 0 B ω t = 0 := by simp

end StatMech.SLE
