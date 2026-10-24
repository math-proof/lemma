/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Kaehler.Polynomial

open scoped TensorProduct
open nonZeroDivisors

noncomputable section

namespace RiemannRochGeneral

/-- Generic rank of an `A`-module `M` (for `A` a domain): the dimension over
`Frac A` of the base-change `Frac A ⊗_A M`. -/
def moduleRank (A : Type*) [CommRing A] [IsDomain A]
    (M : Type*) [AddCommGroup M] [Module A M] : ℕ :=
  Module.finrank (FractionRing A) (FractionRing A ⊗[A] M)

/-- Degree of a maximal ideal `I` of an algebra `A` over `k`: `dim_k (A / I)`. -/
def idealDegree (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra k A] (I : Ideal A) [I.IsMaximal] : ℕ :=
  Module.finrank k (A ⧸ I)

/-- Degree of a line bundle ideal `J` of `A` over `k`: `dim_k (A / J)`. -/
def lineBundleDegree (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] (J : Ideal A) : ℕ :=
  Module.finrank k (A ⧸ J)

/-- Arithmetic genus of a Dedekind algebra `A` over `k`: `dim_k Ω_{A/k}`. -/
def arithmeticGenus (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  Module.finrank k (Ω[A⁄k])
