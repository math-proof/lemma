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
public import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part2

set_option maxHeartbeats 400000

public section


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

section MulMatrix

variable (R : FusionRing ι)
variable (fpd : R.FPdimData)

/-- Existence of the Frobenius-Perron dimension data implies EGNO
Proposition 1.45.5, including that `d` is a positive eigenvector of
each left-multiplication matrix. -/
public theorem proposition_1_45_5 :
    (fpd.d R.unit = 1 ∧
     (∀ i j, fpd.d i * fpd.d j = ∑ k : ι, (R.N i j k : ℝ) * fpd.d k)) ∧
    (∀ X, (R.leftMulMatrixR X).mulVec fpd.d = fpd.d X • fpd.d) ∧
    (∀ i, fpd.d i > 0) := by
  refine ⟨⟨fpd.d_unit, fpd.d_mul⟩, ?eig, fpd.d_pos⟩
  intro X
  ext j
  have hmul := fpd.d_mul X j
  -- (leftMulMatrixR X).mulVec d j = ∑ k, N X j k * d k = d X * d j
  simp [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.smul_apply, smul_eq_mul, leftMulMatrixR]
  exact hmul.symm

end MulMatrix

end FusionRing
