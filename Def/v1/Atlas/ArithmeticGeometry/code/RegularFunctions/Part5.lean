module
public import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Opposites
public import Class.v1.Atlas.ArithmeticGeometry.code.RegularFunctions
open MvPolynomial
set_option autoImplicit false
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable (k : Type*) [Field k]


section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

noncomputable def functionFieldMorphismComponents {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X)) :
    Fin n_cod → FractionRing (AffineCoordinateRingBar X) :=
  fun j => θ (algebraMap (AffineCoordinateRingBar Y)
    (FractionRing (AffineCoordinateRingBar Y))
    (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j)))

end Theorem158
