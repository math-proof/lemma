/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CurveMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Structure.v1.Atlas.EllipticCurves.code.CurveMorphism
open Polynomial

open scoped Polynomial.Bivariate

universe u


namespace CurveMorphism

variable {k : Type u} [Field k]

open ProjectiveCurve

/-- Build a `Morphism` from a rational map together with a proof that it is
regular everywhere. -/
def Morphism.ofIsMorphism {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]
    (φ : ProjectiveCurve.RationalMap f₁ f₂) (h : IsMorphism φ) : Morphism f₁ f₂ :=
  ⟨φ, h⟩

end CurveMorphism
