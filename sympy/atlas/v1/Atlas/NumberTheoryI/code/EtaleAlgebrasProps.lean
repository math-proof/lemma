/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations

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

structure IsEtaleAlgebra (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K L] :
    Prop where
  exists_decomp : ∃ (ι : Type) (_ : Fintype ι) (F : ι → Type)
    (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra K (F i))
    (_ : ∀ i, Algebra.IsSeparable K (F i)),
    Nonempty (L ≃ₐ[K] ∀ i, F i)

def IsFiniteEtaleAlgebra (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K L] :
    Prop :=
  IsEtaleAlgebra K L ∧ Module.Finite K L

section SurjectionsFromProductsOfFields

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]

noncomputable def piRestr (S : Finset ι) :
    (∀ i, F i) →ₐ[K] ∀ i : S, F i where
  toFun f i := f i
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := by ext; simp [Pi.algebraMap_apply]

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma piRestr_apply (S : Finset ι) (f : ∀ i, F i) (j : S) :
    piRestr (K := K) S f j = f j := rfl

noncomputable def algEquivOfSurjSameKer {R A B C : Type*}
    [CommSemiring R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (f : A →ₐ[R] B) (g : A →ₐ[R] C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : RingHom.ker f = RingHom.ker g) : B ≃ₐ[R] C :=
  (Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
    ((Ideal.quotientEquivAlgOfEq R hker).trans (Ideal.quotientKerAlgEquivOfSurjective hg))

abbrev baseChange (A : Type*) [CommRing A]
    (M : Type*) [AddCommGroup M] [Module A M]
    (B : Type*) [CommRing B] [Algebra A B] : Type _ :=
  TensorProduct A B M

instance baseChange.instModule (A : Type*) [CommRing A]
    (M : Type*) [AddCommGroup M] [Module A M]
    (B : Type*) [CommRing B] [Algebra A B] :
    Module B (baseChange A M B) := inferInstance

instance baseChange.instAlgebra (A : Type*) [CommRing A]
    (M : Type*) [CommRing M] [Algebra A M]
    (B : Type*) [CommRing B] [Algebra A B] :
    Algebra B (TensorProduct A B M) := inferInstance

end BaseChange

end EtaleAlgebra
