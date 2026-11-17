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
public import Def.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps.Part2
open scoped Classical

public section

namespace EtaleAlgebra

section SurjectionsFromProductsOfFields

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma piRestr_apply (S : Finset ι) (f : ∀ i, F i) (j : S) :
    piRestr (K := K) S f j = f j := rfl

end SurjectionsFromProductsOfFields
end EtaleAlgebra
