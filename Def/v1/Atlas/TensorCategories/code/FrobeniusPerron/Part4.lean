/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FrobeniusPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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
public import Theorem.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
public import Instance.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part2

@[expose] public section

set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Existence of a Perron–Frobenius eigenpair for any strictly positive
matrix: a positive eigenvalue `r` together with a strictly positive
eigenvector. -/
noncomputable def perronFrobeniusExistence {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v :=
  PerronFrobenius.perronFrobeniusExistence M hM

end FusionRing
