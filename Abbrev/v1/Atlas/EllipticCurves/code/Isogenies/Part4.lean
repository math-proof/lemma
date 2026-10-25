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
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part7
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

section FieldExtensions₄

variable {k : Type u} [Field k]

/-- The projective plane over the function field of a plane curve `f₁`. -/
noncomputable abbrev ProjectivePlaneOfFunctionField (f₁ : k[X][Y])
    [IsDomain (CoordinateRing f₁)] [Fact (Prime f₁)] : Type u :=
  ProjectivePlane (FunctionField f₁)

end FieldExtensions₄
end ProjectiveCurve
