module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FrobeniusPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Def.v1.Atlas.TensorCategories.code.PerronFrobeniusProof.Part2
public import Structure.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part2
public section
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
