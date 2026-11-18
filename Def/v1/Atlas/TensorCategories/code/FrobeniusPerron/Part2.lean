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
public import Class.v1.Atlas.TensorCategories.code.FrobeniusPerron

@[expose] public section
set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

section MulMatrix

variable (R : FusionRing ι)

noncomputable def perron_frobenius_pos_matrix
    [Nonempty ι] [HasPerronFrobeniusProperty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    PerronFrobenius M :=
  let ⟨r, v, hr_pos, hv_pos, hv_eig⟩ := HasPerronFrobeniusProperty.pfEigenvec M hM
  { ev := r
    evec := v
    ev_pos := hr_pos
    evec_pos := hv_pos
    is_eigenvec := hv_eig
    unique := fun μ w hw_pos hw_eig =>
      HasPerronFrobeniusProperty.pfUnique M hM r μ v w hv_pos hv_eig hw_pos hw_eig }

noncomputable def rightMulMatrix : Matrix ι ι ℝ :=
  Matrix.of (fun j k => (∑ i : ι, R.N j i k : ℝ))

noncomputable def leftMulMatrixR (X : ι) : Matrix ι ι ℝ :=
  Matrix.of (fun j k => (R.N X j k : ℝ))

def leftMulMatrixZ (X : ι) : Matrix ι ι ℤ :=
  Matrix.of (fun j k => (R.N X j k : ℤ))

variable (fpd : R.FPdimData)

noncomputable def FPdim : ι → ℝ := fpd.d

noncomputable def catDim : ℝ :=
  ∑ i : ι, fpd.d i ^ 2

end MulMatrix
end FusionRing
