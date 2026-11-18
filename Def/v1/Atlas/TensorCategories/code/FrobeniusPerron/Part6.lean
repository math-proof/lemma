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
public import Theorem.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part4
public import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part5
public import Structure.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part2

@[expose] public section
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
