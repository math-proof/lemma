/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

open scoped Classical


namespace EtaleAlgebra

noncomputable def piSingletonAlgEquiv {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    (j : ι) (hsing : ∀ i : ι, i = j) :
    (∀ i, F i) ≃ₐ[K] F j where
  toFun f := f j
  invFun x i := hsing i ▸ x
  left_inv f := by ext i; have hi := hsing i; subst hi; simp
  right_inv x := by simp
  map_mul' f g := by simp
  map_add' f g := by simp
  commutes' r := by simp [Pi.algebraMap_apply]

end EtaleAlgebra
