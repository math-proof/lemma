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
import Def.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps
open scoped Classical


namespace EtaleAlgebra

structure IsEtaleAlgebra (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K L] :
    Prop where
  exists_decomp : ∃ (ι : Type) (_ : Fintype ι) (F : ι → Type)
    (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra K (F i))
    (_ : ∀ i, Algebra.IsSeparable K (F i)),
    Nonempty (L ≃ₐ[K] ∀ i, F i)

end EtaleAlgebra
