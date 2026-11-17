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
public import Lemma.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
public import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron
public section

set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

section MulMatrix

variable (R : FusionRing ι)

structure FPdimData where
  d : ι → ℝ
  d_unit : d R.unit = 1
  d_pos : ∀ i, d i > 0
  d_mul : ∀ i j, d i * d j = ∑ k : ι, (R.N i j k : ℝ) * d k

structure PerronFrobenius (M : Matrix ι ι ℝ) where
  ev : ℝ
  evec : ι → ℝ
  ev_pos : 0 < ev
  evec_pos : ∀ i, 0 < evec i
  is_eigenvec : M.mulVec evec = ev • evec
  unique : ∀ (μ : ℝ) (w : ι → ℝ), (∀ i, 0 < w i) →
    M.mulVec w = μ • w →
    ∃ c : ℝ, ∀ i, w i = c * evec i

end MulMatrix
end FusionRing
