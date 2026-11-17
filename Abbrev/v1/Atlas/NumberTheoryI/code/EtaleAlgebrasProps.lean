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
public import Def.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps.Part3
@[expose] public section

open scoped Classical


namespace EtaleAlgebra

section SurjectionsFromProductsOfFields

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]

abbrev baseChange (A : Type*) [CommRing A]
    (M : Type*) [AddCommGroup M] [Module A M]
    (B : Type*) [CommRing B] [Algebra A B] : Type _ :=
  TensorProduct A B M

end SurjectionsFromProductsOfFields
end EtaleAlgebra
