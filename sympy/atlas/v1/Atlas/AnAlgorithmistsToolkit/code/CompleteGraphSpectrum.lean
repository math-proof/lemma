/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CompleteGraphSpectrum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.GraphMatrices
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace CompleteGraphSpectrum

open Matrix SimpleGraph Finset BigOperators Module

noncomputable def completeGraphLapEnd (n : ℕ) : Module.End ℝ (Fin n → ℝ) :=
  Matrix.toLin' ((completeGraph (Fin n)).lapMatrix ℝ)

noncomputable def sumFunctional (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ j, v j
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.mul_sum]
