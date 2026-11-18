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

@[expose] public noncomputable section
set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

namespace PerronFrobeniusFin2

open FusionRing

noncomputable section

/-- Discriminant of the characteristic polynomial of a 2×2 matrix,
`(M₀₀ - M₁₁)² + 4 M₀₁ M₁₀`. -/
def pfDiscriminant (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0

/-- The larger root of the characteristic polynomial of a 2×2 matrix,
the candidate Perron–Frobenius eigenvalue. -/
def pfEigenvalue (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (M 0 0 + M 1 1 + Real.sqrt (pfDiscriminant M)) / 2

/-- Explicit Perron–Frobenius eigenvector of a 2×2 matrix,
`(M 0 1, pfEigenvalue M - M 0 0)`. -/
def pfEigenvec (M : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → ℝ :=
  ![M 0 1, pfEigenvalue M - M 0 0]

end
end PerronFrobeniusFin2
end FusionRing
