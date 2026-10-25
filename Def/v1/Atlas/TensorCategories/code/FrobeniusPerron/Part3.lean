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
import Instance.v1.Atlas.TensorCategories.code.FrobeniusPerron
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
