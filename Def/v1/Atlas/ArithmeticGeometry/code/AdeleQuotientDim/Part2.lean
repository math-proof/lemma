/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part6
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RiemannRoch
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Finsupp
import Abbrev.v1.Atlas.ArithmeticGeometry.code.AdeleQuotientDim
open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily


section ChainFormula

variable {R : Type*} [DivisionRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Combinatorial distance between divisors: $\sum_p (B - A)(p)$, truncated to
$\mathbb{N}$. Used as a strong-induction measure in the proof of Lemma 22.8. -/
noncomputable def divisorDistance (A B : P →₀ ℤ) : ℕ :=
  ((B - A).sum (fun _ n => n)).toNat

end ChainFormula
