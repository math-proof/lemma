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
import Structure.v1.Atlas.TensorCategories.code.FrobeniusPerron
set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

section Basic

variable (R : FusionRing ι)

def IsAntiAutomorphism (ψ : ι → ι) : Prop :=
  Function.Bijective ψ ∧
  ∀ i j k, R.N (ψ i) j k = R.N i k j

def IsTransitive : Prop :=
  (∀ X Z : ι, ∃ Y : ι, 0 < R.N X Y Z) ∧
  (∀ X Z : ι, ∃ Y : ι, 0 < R.N Y X Z)

end Transitivity

section MulMatrix

variable (R : FusionRing ι)

def mulMatrix (i : ι) : Matrix ι ι ℕ :=
  Matrix.of (fun j k => R.N i j k)

def IsComplexEigenvalue (M : Matrix ι ι ℝ) (μ : ℂ) : Prop :=
  ∃ v : ι → ℂ, v ≠ 0 ∧
    (M.map (↑· : ℝ → ℂ)).mulVec v = μ • v

end MulMatrix
end FusionRing
