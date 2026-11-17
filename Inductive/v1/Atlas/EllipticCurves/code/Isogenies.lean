/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part4
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- A projective point on the curve `f₀ = 0` over an extension field `K`, either an
affine point or a point at infinity given by a nonzero direction `(a, b)`. -/
public inductive ProjectiveCurvePointOver (f₀ : k[X][Y]) (K : Type u) [Field K] [Algebra k K]
  |     affine : AffinePointOver f₀ K → ProjectiveCurvePointOver f₀ K
  |     atInfinity : (a : K) → (b : K) → (a ≠ 0 ∨ b ≠ 0) →
      ProjectiveCurvePointOver f₀ K

end ProjectiveCurve
