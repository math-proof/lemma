/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.FieldTheory.SeparableDegree
import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part4
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IsogenyKernels
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lemma53
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
import Def.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part9
open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

open Polynomial

/-- Auxiliary statement for prime-degree factorisation: any divisor $d$ of $\alpha$.degree
admits a length-$2$ decomposition with degrees $p$ and $d/p$. -/
inductive IsogenyChain {F : Type*} [Field F] [DecidableEq F] :
    WeierstrassCurve.Affine F → WeierstrassCurve.Affine F → Type _ where
  | single {E₁ E₂ : WeierstrassCurve.Affine F} (φ : Isogeny E₁ E₂) :
      IsogenyChain E₁ E₂
  | cons {E₁ E₂ E₃ : WeierstrassCurve.Affine F} (φ : Isogeny E₁ E₂)
      (rest : IsogenyChain E₂ E₃) : IsogenyChain E₁ E₃

end ShortWeierstrassCurve
