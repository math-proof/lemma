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
import Class.v1.Atlas.TensorCategories.code.FrobeniusPerron
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

noncomputable def FPdim : ι → ℝ := fpd.d

noncomputable def catDim : ℝ :=
  ∑ i : ι, fpd.d i ^ 2

end MulMatrix
end FusionRing
