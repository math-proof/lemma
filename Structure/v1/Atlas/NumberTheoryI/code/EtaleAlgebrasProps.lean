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
public import Def.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps
public section

open scoped Classical


namespace EtaleAlgebra

structure IsEtaleAlgebra (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K L] :
    Prop where
  exists_decomp : ∃ (ι : Type) (_ : Fintype ι) (F : ι → Type)
    (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra K (F i))
    (_ : ∀ i, Algebra.IsSeparable K (F i)),
    Nonempty (L ≃ₐ[K] ∀ i, F i)

end EtaleAlgebra
