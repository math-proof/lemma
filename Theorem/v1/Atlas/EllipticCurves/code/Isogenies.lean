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
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part8
open Polynomial

open scoped Polynomial.Bivariate

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
