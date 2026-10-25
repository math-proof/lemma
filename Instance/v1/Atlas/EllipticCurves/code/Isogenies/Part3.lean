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
import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part6
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace Isogeny

variable {F : Type u} [Field F] [DecidableEq F]

variable {E₁ E₂ E₃ : WeierstrassCurve.Affine F}

/-- An isogeny may be applied to points like a function. -/
instance : CoeFun (Isogeny E₁ E₂) (fun _ => E₁.Point → E₂.Point) where
  coe φ := φ.toAddMonoidHom

end Isogeny
