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
import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part5
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

/-- The degree of an isogeny in standard form: `deg α := max (deg u) (deg v)`
(see Definition for Theorem 5.22 / standard-form degree). -/
noncomputable def degree (α : IsogenyStandardForm F) : ℕ :=
  max α.u.natDegree α.v.natDegree

/-- An isogeny in standard form is *separable* if `u'v - uv' ≠ 0`. -/
def IsSeparable (α : IsogenyStandardForm F) : Prop :=
  Polynomial.derivative α.u * α.v - α.u * Polynomial.derivative α.v ≠ 0

/-- An isogeny is *inseparable* if it is not separable. -/
def IsInseparable (α : IsogenyStandardForm F) : Prop :=
  ¬ α.IsSeparable

end IsogenyStandardForm
