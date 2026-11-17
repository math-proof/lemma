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
public import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part8
open Polynomial

open scoped Polynomial.Bivariate

public section

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

example : (⟨Polynomial.X, 1, 1, 1,
    one_ne_zero, one_ne_zero,
    isCoprime_one_right, isCoprime_one_right⟩ : IsogenyStandardForm F).degree = 1 := by
  simp [degree, Polynomial.natDegree_X, Polynomial.natDegree_one]

example : (⟨Polynomial.X, 1, 1, 1,
    one_ne_zero, one_ne_zero,
    isCoprime_one_right, isCoprime_one_right⟩ : IsogenyStandardForm F).IsSeparable := by
  simp [IsSeparable, Polynomial.derivative_X, Polynomial.derivative_one]

end IsogenyStandardForm
