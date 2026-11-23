/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Opposites
public import Instance.v1.Atlas.ArithmeticGeometry.code.RegularFunctions
public section

open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Corollary159

variable (k : Type*) [Field k]

open MvPolynomial CategoryTheory

/-- Bundled object of the category of affine varieties (over $\bar k$) with domain
coordinate ring: packages a dimension, a carrier set, the algebraic-subset condition,
and the integral-domain property of $\bar k[X]$. -/
structure AffineVarietyDom where
  dim : ℕ
  carrier : Set (Fin dim → AlgebraicClosure k)
  isAlgebraic : IsAlgebraicSubset k dim carrier
  isDomain : IsDomain (AffineCoordinateRingBar carrier)

attribute [instance] AffineVarietyDom.isDomain

/-- A morphism in `AffineVarietyDom k`: a dominant rational map between the underlying
varieties, bundling a rational map and a proof that it is dominant. -/
@[ext]
structure AffineVarietyDom.Hom (V W : AffineVarietyDom k) where
  map : @AffineRationalMap k _ V.dim W.dim V.carrier W.carrier V.isDomain
  dominant : @IsDominantRationalMap k _ V.dim W.dim V.carrier
    V.isDomain W.carrier map

end Corollary159
