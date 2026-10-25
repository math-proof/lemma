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
import Instance.v1.Atlas.LieGroups.code.SL2Basics
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

theorem basisH_C_mem_sl2C : basisH_C ∈ sl2C := by
  show (Matrix.traceLinearMap (Fin 2) ℂ ℂ) basisH_C = 0
  simp [basisH_C, Matrix.traceLinearMap, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem basisE_C_mem_sl2C : basisE_C ∈ sl2C := by
  show (Matrix.traceLinearMap (Fin 2) ℂ ℂ) basisE_C = 0
  simp [basisE_C, Matrix.traceLinearMap, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem basisF_C_mem_sl2C : basisF_C ∈ sl2C := by
  show (Matrix.traceLinearMap (Fin 2) ℂ ℂ) basisF_C = 0
  simp [basisF_C, Matrix.traceLinearMap, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

end
