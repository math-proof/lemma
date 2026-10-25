/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrothendieckGroup
import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckGroup.Part3
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Dimension.Finrank
open scoped TensorProduct
open nonZeroDivisors


noncomputable section

namespace RiemannRochCurves

/-- Euler characteristic packaged as an integer, defaulting to `1 - g_a`
(the value at the structure sheaf). -/
def eulerChar (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (structureSheafEuler : ℤ := 1 - (RiemannRochGeneral.arithmeticGenus k A : ℤ)) :
    ℤ := structureSheafEuler

/-- Genus of a curve presented by an affine Dedekind algebra: defined as
`dim_k Ω_{A/k}`. -/
def curveGenus (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- Degree of an ideal `I` of `A`: `dim_k (A / I)`. -/
def idealDeg (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] (I : Ideal A) : ℕ :=
  Module.finrank k (A ⧸ I)

/-- Generic rank of an `A`-module `M` (for `A` a domain): the dimension over
`Frac A` of the base-change `Frac A ⊗_A M`. -/
def moduleRk (A : Type*) [CommRing A] [IsDomain A]
    (M : Type*) [AddCommGroup M] [Module A M] : ℕ :=
  Module.finrank (FractionRing A) (FractionRing A ⊗[A] M)


/-- The Riemann–Roch additive homomorphism for genus `g`:
`(r, d) ↦ d - r(g - 1)`. -/
def rrHom (g : ℤ) : ℤ × ℤ →+ ℤ where
  toFun p := p.2 - p.1 * (g - 1)
  map_zero' := by simp
  map_add' := by intro ⟨r₁, d₁⟩ ⟨r₂, d₂⟩; simp; ring


end RiemannRochCurves
end
