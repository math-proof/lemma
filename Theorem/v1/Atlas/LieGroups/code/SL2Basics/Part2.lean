/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Abelian
import Def.v1.Atlas.LieGroups.code.SL2Basics.Part2
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

open Module Fintype in
theorem finrank_sl2C : Module.finrank ℂ sl2C = 3 := by
  suffices h : Module.finrank ℂ (LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ)) = 3 from h
  have h_surj : Function.Surjective (Matrix.traceLinearMap (Fin 2) ℂ ℂ) := by
    intro c
    exact ⟨Matrix.diagonal (fun i => if i = 0 then c else 0), by
      simp [Matrix.traceLinearMap, Matrix.trace, Matrix.diag]⟩
  have key := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  rw [LinearMap.range_eq_top.mpr h_surj, finrank_top, Module.finrank_matrix] at key
  simp [Fintype.card_fin, finrank_self] at key
  omega

open Module Fintype in
theorem finrank_sl2R : Module.finrank ℝ sl2R = 3 := by
  suffices h : Module.finrank ℝ (LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℝ ℝ)) = 3 from h
  have h_surj : Function.Surjective (Matrix.traceLinearMap (Fin 2) ℝ ℝ) := by
    intro c
    exact ⟨Matrix.diagonal (fun i => if i = 0 then c else 0), by
      simp [Matrix.traceLinearMap, Matrix.trace, Matrix.diag]⟩
  have key := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 2) ℝ ℝ)
  rw [LinearMap.range_eq_top.mpr h_surj, finrank_top, Module.finrank_matrix] at key
  simp [Fintype.card_fin, finrank_self] at key
  omega

end
