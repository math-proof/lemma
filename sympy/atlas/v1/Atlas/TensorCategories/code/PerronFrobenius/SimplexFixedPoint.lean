/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobenius/SimplexFixedPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.PerronFrobeniusProof
import Lemma.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
import Mathlib.Analysis.Normed.Field.Basic

open Matrix Finset BigOperators

namespace PerronFrobenius

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]

/-- Existence of a positive Perron-Frobenius eigenvector and eigenvalue for a strictly
positive matrix, packaged through the simplex fixed-point construction. -/
noncomputable def simplexFixedPoint_pos_matrix
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v :=
  perronFrobeniusExistence M hM

/-- A nonnegative matrix admits a nonnegative eigenvalue and a nonnegative eigenvector
with at least one strictly positive coordinate. -/
end PerronFrobenius
