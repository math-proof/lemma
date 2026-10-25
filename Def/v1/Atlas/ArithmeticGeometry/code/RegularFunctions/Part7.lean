/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Opposites
import Theorem.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part4
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

/-- Scalar extension on function fields: the natural homomorphism $k(X) \to \bar k(X)$
obtained by extending the coordinate-ring map $k[X] \to \bar k[X]$ to fraction fields. -/
noncomputable def functionFieldToBar {n : ℕ}
    (X : Set (Fin n → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRing X)] :
    FractionRing (AffineCoordinateRing X) →+*
    FractionRing (AffineCoordinateRingBar X) :=
  IsFractionRing.lift
    (g := (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
      (coordRingToBar X))
    (coordRingToBar_comp_algebraMap_injective X)

/-- A rational map $\varphi : X \dashrightarrow Y$ is *defined over $k$* if each of its
components lies in the image of $k(X) \to \bar k(X)$, i.e. can be represented by a tuple
of rational functions with coefficients in the base field $k$. -/
def AffineRationalMap.IsDefinedOverK {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRing X)]
    (φ : AffineRationalMap X Y) : Prop :=
  ∀ j : Fin n_cod, φ.components j ∈
    Set.range (functionFieldToBar X)

end Theorem158
