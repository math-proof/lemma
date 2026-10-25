/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CurveMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Def.v1.Atlas.EllipticCurves.code.CurveMorphism
open Polynomial

open scoped Polynomial.Bivariate

universe u


namespace CurveMorphism

variable {k : Type u} [Field k]

open ProjectiveCurve

/-- The type of `K`-points of the projective curve cut out by `f₀`, encoded as
either an affine point or a point at infinity given by projective coordinates
`(a : b : 0)` with `(a, b)` not both zero. -/
inductive ProjectiveCurvePointOver (f₀ : k[X][Y]) (K : Type u) [Field K] [Algebra k K]
  |     affine : AffinePointOver f₀ K → ProjectiveCurvePointOver f₀ K
  |     atInfinity : (a : K) → (b : K) → (a ≠ 0 ∨ b ≠ 0) →
      ProjectiveCurvePointOver f₀ K

end CurveMorphism
