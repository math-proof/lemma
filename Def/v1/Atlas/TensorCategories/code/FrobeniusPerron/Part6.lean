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
import Theorem.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part4
set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- EGNO Theorem 1.44.1 (Perron–Frobenius for strictly positive
matrices): existence and uniqueness of a Perron–Frobenius eigenpair,
bundled as a `PerronFrobenius M`. -/
noncomputable def theorem_1_44_1
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    FusionRing.PerronFrobenius M :=
  let ⟨r, v, hr_pos, hv_pos, hv_eig⟩ := theorem_1_44_1_existence M hM
  { ev := r
    evec := v
    ev_pos := hr_pos
    evec_pos := hv_pos
    is_eigenvec := hv_eig
    unique := fun μ w hw_pos hw_eig =>
      theorem_1_44_1_uniqueness M hM r μ v w hv_pos hv_eig hw_pos hw_eig }

end FusionRing
