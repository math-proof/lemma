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
import Abbrev.v1.Atlas.LieGroups.code.SL2Basics
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

def sl2R : LieSubalgebra ℝ M2 where
  toSubmodule := (Matrix.traceLinearMap (Fin 2) ℝ ℝ).ker
  lie_mem' := by
    intro x y hx hy
    change (Matrix.traceLinearMap (Fin 2) ℝ ℝ) x = 0 at hx
    change (Matrix.traceLinearMap (Fin 2) ℝ ℝ) y = 0 at hy
    show (Matrix.traceLinearMap (Fin 2) ℝ ℝ) ⁅x, y⁆ = 0
    simp only [Ring.lie_def, map_sub, Matrix.traceLinearMap_apply]
    rw [Matrix.trace_mul_comm]; ring

def basisH : M2 := !![1, 0; 0, -1]

def basisE : M2 := !![0, 1; 0, 0]

def basisF : M2 := !![0, 0; 1, 0]

def sl2C : LieSubalgebra ℂ M2C where
  toSubmodule := (Matrix.traceLinearMap (Fin 2) ℂ ℂ).ker
  lie_mem' := by
    intro x y hx hy
    change (Matrix.traceLinearMap (Fin 2) ℂ ℂ) x = 0 at hx
    change (Matrix.traceLinearMap (Fin 2) ℂ ℂ) y = 0 at hy
    show (Matrix.traceLinearMap (Fin 2) ℂ ℂ) ⁅x, y⁆ = 0
    simp only [Ring.lie_def, map_sub, Matrix.traceLinearMap_apply]
    rw [Matrix.trace_mul_comm]; ring

def basisH_C : M2C := !![1, 0; 0, -1]

def basisE_C : M2C := !![0, 1; 0, 0]

def basisF_C : M2C := !![0, 0; 1, 0]

end
