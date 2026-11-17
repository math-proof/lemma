/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutGenus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutIntersection
public import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutIntersection
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Algebra.Module.SpanRank


public noncomputable section

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

end BezoutGenus
end
