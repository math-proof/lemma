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
import Def.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps.Part3
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
