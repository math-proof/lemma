/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutGenus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.BezoutIntersection
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutIntersection
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Module.SpanRank

noncomputable section

open Polynomial BezoutIntersection

namespace BezoutGenus

variable (k : Type*) [Field k]

/-- Bundle of data for a smooth projective curve over `k`: a Dedekind coordinate ring (as an
algebra over `k`) together with its arithmetic genus. -/
structure SmoothProjectiveCurveWithCoords (k : Type*) [Field k] where
  CoordinateRing : Type*
  [instCommRing : CommRing CoordinateRing]
  [instAlgebra : Algebra k CoordinateRing]
  [instIsDomain : IsDomain CoordinateRing]
  [instIsDedekind : IsDedekindDomain CoordinateRing]
  genus : ℕ

attribute [instance] SmoothProjectiveCurveWithCoords.instCommRing
  SmoothProjectiveCurveWithCoords.instAlgebra
  SmoothProjectiveCurveWithCoords.instIsDomain
  SmoothProjectiveCurveWithCoords.instIsDedekind

/-- Existence of the Jacobian of a smooth projective curve `X` of genus `g`: a `k`-vector space
`J` of dimension `g` containing a discrete abelian subgroup `Λ ≅ ℤ^{2g}`. -/
def bivariateResultant (f g : k[X][X]) : k[X] :=
  Polynomial.resultant f g

/-- The arithmetic genus of a smooth plane curve of degree `d`, equal to `(d-1)(d-2)/2`. -/
def genusOfSmoothPlaneCurve (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

end BezoutGenus
