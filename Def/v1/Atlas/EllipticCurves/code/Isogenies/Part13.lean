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
import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part9
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

namespace Isogeny

variable {F : Type u} [Field F] [DecidableEq F]

variable {E₁ E₂ : WeierstrassCurve.Affine F}

open Polynomial

/-- Extract the affine coordinates `(x, y)` of a point of `E₁`, mapping the
identity to `none`. -/
noncomputable def pointToCoords : E₁.Point → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

end Isogeny
end IsogenyStandardForm
