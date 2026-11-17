/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Theorem.v1.Atlas.EllipticCurves.code.Isogenies.Part2

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

namespace WithCurveData

variable (α : WithCurveData F)

/-- `RationalMapTriple` modulo equivalence is a `Setoid`, provided `(f₁)` is
prime so that transitivity holds. -/
instance RationalMapTriple.setoid {k : Type u} [CommRing k]
    (f₁ f₂ : MvPolynomial (Fin 3) k)
    [hprime : Fact ((Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))).IsPrime)] :
    Setoid (RationalMapTriple f₁ f₂) where
  r := RationalMapTriple.IsEquiv
  iseqv :=
    ⟨fun t => RationalMapTriple.isEquiv_refl t,
     fun h => RationalMapTriple.isEquiv_symm h,
     fun h1 h2 => RationalMapTriple.isEquiv_trans_of_prime hprime.out h1 h2⟩

end WithCurveData
end IsogenyStandardForm
