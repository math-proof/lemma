/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CurveMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Def.v1.Atlas.EllipticCurves.code.CurveMorphism.Part2
open Polynomial

open scoped Polynomial.Bivariate

universe u


namespace CurveMorphism

variable {k : Type u} [Field k]

open ProjectiveCurve

/-- A morphism of projective curves from `f₁` to `f₂`: a rational map together
with a proof that it is regular everywhere. Corresponds to the notion of morphism
of curves in Definition 4.14. -/
structure Morphism (f₁ f₂ : k[X][Y]) [IsDomain (CoordinateRing f₁)] where
  toRationalMap : ProjectiveCurve.RationalMap f₁ f₂
  regular_everywhere : IsMorphism toRationalMap

end CurveMorphism
