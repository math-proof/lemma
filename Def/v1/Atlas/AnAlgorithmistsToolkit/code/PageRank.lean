/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Data.Real.Basic
open scoped Matrix BigOperators
open Matrix Finset


namespace PageRank

variable {n : ℕ}

noncomputable def pageRankVec (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) :
    Fin n → ℝ :=
  ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹ *ᵥ (α • s)

noncomputable def l1norm (f : Fin n → ℝ) : ℝ := ∑ i, |f i|

noncomputable def vol (d : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ x ∈ S, d x

noncomputable def vecSupp (f : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => f v ≠ 0)

end PageRank
