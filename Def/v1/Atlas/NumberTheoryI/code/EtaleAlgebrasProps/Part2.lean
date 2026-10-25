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
import Structure.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps
open scoped Classical


namespace EtaleAlgebra

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

end SurjectionsFromProductsOfFields
end EtaleAlgebra
