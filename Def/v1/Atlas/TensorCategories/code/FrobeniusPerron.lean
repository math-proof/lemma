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
public import Structure.v1.Atlas.TensorCategories.code.FrobeniusPerron

@[expose] public section
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

end Basic

section MulMatrix

variable (R : FusionRing ι)

def mulMatrix (i : ι) : Matrix ι ι ℕ :=
  Matrix.of (fun j k => R.N i j k)

def IsComplexEigenvalue (M : Matrix ι ι ℝ) (μ : ℂ) : Prop :=
  ∃ v : ι → ℂ, v ≠ 0 ∧
    (M.map (↑· : ℝ → ℂ)).mulVec v = μ • v

end MulMatrix
end FusionRing
