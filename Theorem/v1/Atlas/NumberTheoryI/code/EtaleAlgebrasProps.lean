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
import Def.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps.Part2
open scoped Classical


namespace EtaleAlgebra

section SurjectionsFromProductsOfFields

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma piRestr_apply (S : Finset ι) (f : ∀ i, F i) (j : S) :
    piRestr (K := K) S f j = f j := rfl

end SurjectionsFromProductsOfFields
end EtaleAlgebra
