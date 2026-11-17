/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.FieldTheory.SeparableDegree
public import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part4
public import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
public import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
public import Def.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part9
open Polynomial
open scoped Polynomial.Bivariate

namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

open Polynomial

/-- Auxiliary statement for prime-degree factorisation: any divisor $d$ of $\alpha$.degree
admits a length-$2$ decomposition with degrees $p$ and $d/p$. -/
public inductive IsogenyChain {F : Type*} [Field F] [DecidableEq F] :
    WeierstrassCurve.Affine F → WeierstrassCurve.Affine F → Type _ where
  | single {E₁ E₂ : WeierstrassCurve.Affine F} (φ : Isogeny E₁ E₂) :
      IsogenyChain E₁ E₂
  | cons {E₁ E₂ E₃ : WeierstrassCurve.Affine F} (φ : Isogeny E₁ E₂)
      (rest : IsogenyChain E₂ E₃) : IsogenyChain E₁ E₃

end ShortWeierstrassCurve
