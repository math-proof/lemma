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
import Theorem.v1.Atlas.EllipticCurves.code.Isogenies.Part2
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
