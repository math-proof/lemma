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
import Def.v1.Atlas.LieGroups.code.SL2Basics
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

theorem lie_H_E_C : ⁅basisH_C, basisE_C⁆ = 2 • basisE_C := by
  simp only [Ring.lie_def, basisH_C, basisE_C]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]; ring

theorem lie_H_F_C : ⁅basisH_C, basisF_C⁆ = (-2) • basisF_C := by
  simp only [Ring.lie_def, basisH_C, basisF_C]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]; ring

theorem lie_E_F_C : ⁅basisE_C, basisF_C⁆ = basisH_C := by
  simp only [Ring.lie_def, basisE_C, basisF_C, basisH_C]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end
