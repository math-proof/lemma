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
public import Theorem.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps

@[expose] public section

open scoped Classical


namespace EtaleAlgebra

section SurjectionsFromProductsOfFields

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]

noncomputable def algEquivOfSurjSameKer {R A B C : Type*}
    [CommSemiring R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (f : A →ₐ[R] B) (g : A →ₐ[R] C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : RingHom.ker f = RingHom.ker g) : B ≃ₐ[R] C :=
  (Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
    ((Ideal.quotientEquivAlgOfEq R hker).trans (Ideal.quotientKerAlgEquivOfSurjective hg))

end SurjectionsFromProductsOfFields
end EtaleAlgebra
