/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.Abelian
public import Def.v1.Atlas.LieGroups.code.SL2Basics.Part2

public section

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
