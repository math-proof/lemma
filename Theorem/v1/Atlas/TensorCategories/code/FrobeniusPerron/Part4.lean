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
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part5
set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Uniqueness part of EGNO Theorem 1.44.1: any two positive
eigenvectors of a strictly positive matrix are scalar multiples
of each other. -/
theorem theorem_1_44_1_uniqueness
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j)
    (r₁ r₂ : ℝ) (v w : ι → ℝ)
    (hv : ∀ i, 0 < v i) (hev : M.mulVec v = r₁ • v)
    (hw : ∀ i, 0 < w i) (hew : M.mulVec w = r₂ • w) :
    ∃ c : ℝ, ∀ i, w i = c * v i :=
  PerronFrobeniusGeneral.pfUnique_general M hM r₁ r₂ v w hv hev hw hew

end FusionRing
