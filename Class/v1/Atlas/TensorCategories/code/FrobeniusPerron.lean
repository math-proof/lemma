/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FrobeniusPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Def.v1.Atlas.TensorCategories.code.PerronFrobeniusProof.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
import Structure.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part2
set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

section MulMatrix

variable (R : FusionRing ι)

class HasPerronFrobeniusProperty (ι : Type*) [DecidableEq ι] [Fintype ι] [Nonempty ι] where
  pfEigenvec : ∀ (M : Matrix ι ι ℝ), (∀ i j, 0 < M i j) →
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v
  pfUnique : ∀ (M : Matrix ι ι ℝ), (∀ i j, 0 < M i j) →
    ∀ (r₁ r₂ : ℝ) (v w : ι → ℝ),
    (∀ i, 0 < v i) → M.mulVec v = r₁ • v →
    (∀ i, 0 < w i) → M.mulVec w = r₂ • w →
    ∃ c : ℝ, ∀ i, w i = c * v i

end MulMatrix
end FusionRing
