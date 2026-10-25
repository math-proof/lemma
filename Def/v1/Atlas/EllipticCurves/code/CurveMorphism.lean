/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CurveMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
open Polynomial

open scoped Polynomial.Bivariate

universe u


namespace CurveMorphism

variable {k : Type u} [Field k]

open ProjectiveCurve

/-- Predicate asserting that a function field element `φ` on the affine curve
defined by `f₀` is regular and nonzero at an affine point `P` over an extension `K`:
there is a representation `φ = g / h` with both `h(P)` and `g(P)` nonzero. -/
def IsRegularNonzeroAtOver {f₀ : k[X][Y]} {K : Type u}
    [Field K] [Algebra k K]
    (φ : FunctionField f₀) (P : AffinePointOver f₀ K) : Prop :=
  ∃ (g : CoordinateRing f₀) (h : ↥(nonZeroDivisors (CoordinateRing f₀))),
    φ = IsLocalization.mk' (FunctionField f₀) g h ∧
    P.evalRingHom (h : CoordinateRing f₀) ≠ 0 ∧
    P.evalRingHom g ≠ 0

/-- Predicate asserting that the projective rational map `φ` from the curve `f₁`
to the curve `f₂` is regular at an affine point `P`: there exists a nonzero common
scaling `μ` so that all three coordinate components are regular at `P` and at least
one is nonzero (so the resulting projective point is well-defined). -/
def IsRegularAtOver {f₁ f₂ : k[X][Y]}
    [IsDomain (CoordinateRing f₁)]
    (φ : ProjectiveCurve.RationalMap f₁ f₂) {K : Type u} [Field K] [Algebra k K]
    (P : AffinePointOver f₁ K) : Prop :=
  ∃ (μ : FunctionField f₁), μ ≠ 0 ∧
    (μ * φ.φ₁).IsRegularAtOver P ∧
    (μ * φ.φ₂).IsRegularAtOver P ∧
    (μ * φ.φ₃).IsRegularAtOver P ∧
    (IsRegularNonzeroAtOver (μ * φ.φ₁) P ∨
     IsRegularNonzeroAtOver (μ * φ.φ₂) P ∨
     IsRegularNonzeroAtOver (μ * φ.φ₃) P)

end CurveMorphism
