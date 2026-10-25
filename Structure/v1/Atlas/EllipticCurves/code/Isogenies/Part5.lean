/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic
import Abbrev.v1.Atlas.EllipticCurves.code.Isogenies.Part4
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

