/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/JordanForm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Matrix.Block
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Algebra.Polynomial.Module.FiniteDimensional
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

@[expose] public section

namespace JordanForm

open Matrix Finset Module

section NilpotentLinearMap

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

def IsNilpotentOperator (T : Module.End R M) : Prop :=
  ∃ m : ℕ, T ^ m = 0

end NilpotentLinearMap

section JordanBlock

variable {F : Type*} [Field F]

def jordanBlock (a : ℕ) (μ : F) : Matrix (Fin a) (Fin a) F :=
  Matrix.of fun (i j : Fin a) =>
    if (i : ℕ) = (j : ℕ) then μ
    else if (i : ℕ) + 1 = (j : ℕ) then 1
    else 0

end JordanBlock

section JordanNormalForm

variable {F : Type*} [Field F]

def jordanNormalForm {r : ℕ} [DecidableEq (Fin r)]
    (blockSize : Fin r → ℕ) (μ : Fin r → F) :
    Matrix ((i : Fin r) × Fin (blockSize i)) ((i : Fin r) × Fin (blockSize i)) F :=
  Matrix.blockDiagonal' (fun i => jordanBlock (blockSize i) (μ i))

noncomputable def jordanMatrix {r : ℕ} [DecidableEq (Fin r)]
    (blockSize : Fin r → ℕ) (μ : Fin r → F)
    {n : ℕ} (hsum : ∑ i : Fin r, blockSize i = n) :
    Matrix (Fin n) (Fin n) F :=
  (Matrix.reindex (finSigmaFinEquiv.trans (finCongr hsum))
    (finSigmaFinEquiv.trans (finCongr hsum)))
    (jordanNormalForm blockSize μ)

end JordanNormalForm
end JordanForm
