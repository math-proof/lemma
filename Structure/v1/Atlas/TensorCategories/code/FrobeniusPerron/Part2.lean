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
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron
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
