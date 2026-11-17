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
public import Abbrev.v1.Atlas.EllipticCurves.code.Isogenies.Part4
public section

open Polynomial

open scoped Polynomial.Bivariate

universe u v


/-- Data for an isogeny `α : E₁ → E₂` in *standard form*: rational functions
`u, v, s, t ∈ F[X]` such that the `x`-coordinate transforms as `u/v` and the
`y`-coordinate transforms as `(s/t)·y`, with the coprimality and nonvanishing
conditions required for this to be in lowest terms. -/
structure IsogenyStandardForm (F : Type u) [Field F] where
  u : F[X]
  v : F[X]
  s : F[X]
  t : F[X]
  v_ne_zero : v ≠ 0
  t_ne_zero : t ≠ 0
  coprime_uv : IsCoprime u v
  coprime_st : IsCoprime s t

