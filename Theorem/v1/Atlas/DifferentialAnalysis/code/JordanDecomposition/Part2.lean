/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Def.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition.Part2


namespace ContinuousFunctions

open ContinuousLinearMap

section PosPartConstruction

variable {X : Type*} [MetricSpace X]

/-- For nonnegative `f`, the set `posPartSet u f` is nonempty, witnessed by the choice `g = 0`. -/
lemma posPartSet_nonempty (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (hf : ∀ x, 0 ≤ f x) :
    (posPartSet u f).Nonempty :=
  ⟨u 0, 0, fun _ => le_refl 0, hf, by simp [map_zero]⟩

/-- The set `posPartSet u f` is bounded above by `‖u‖ * ‖f‖`. -/
lemma posPartSet_bddAbove (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (_hf : ∀ x, 0 ≤ f x) :
    BddAbove (posPartSet u f) := by
  refine ⟨‖u‖ * ‖f‖, fun r ⟨g, hg0, hgf, hr⟩ => ?_⟩; rw [hr]
  calc u g ≤ |u g| := le_abs_self _
    _ = ‖u g‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖u‖ * ‖g‖ := le_opNorm u g
    _ ≤ ‖u‖ * ‖f‖ :=
        mul_le_mul_of_nonneg_left (c0_norm_le_of_nonneg_le f g hg0 hgf) (norm_nonneg u)

end PosPartConstruction
end ContinuousFunctions
