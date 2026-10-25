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
import Abbrev.v1.Atlas.EllipticCurves.code.Isogenies.Part5
open Polynomial

open scoped Polynomial.Bivariate

universe u v


/-- An isogeny `E₁ → E₂` between Weierstrass curves: a surjective group
homomorphism between their group-of-points along with a positive integer
"degree" attribute. (See Sutherland, definitions surrounding §5.1 — an isogeny
is a surjective morphism of elliptic curves that sends the identity to the
identity.) -/
structure Isogeny {F : Type u} [Field F] [DecidableEq F]
    (E₁ E₂ : WeierstrassCurve.Affine F) where
  toAddMonoidHom : E₁.Point →+ E₂.Point
  surjective : Function.Surjective toAddMonoidHom
  degree : ℕ
  degree_pos : 0 < degree

