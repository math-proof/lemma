/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec9Blowups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
open Polynomial


namespace Lec9Blowups

/-- The blowup (Rees) algebra `⨁_{n ≥ 0} 𝔪ⁿ tⁿ ⊆ A[t]` of the ideal
`𝔪 ⊆ A` (Lec 9, Def 20). -/
def blowupAlgebra (A : Type*) [CommRing A] (𝔪 : Ideal A) : Subalgebra A A[X] :=
  reesAlgebra 𝔪

end Lec9Blowups
