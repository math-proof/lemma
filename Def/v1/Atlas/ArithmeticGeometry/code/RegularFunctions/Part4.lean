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
import Theorem.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part2
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

/-- Descent of the substitution homomorphism to a ring map $\bar k[Y] \to \bar k(X)$:
since the substitution kills $\mathcal{I}(Y)$, it factors through the quotient
$\bar k[Y_1,\dots,Y_{n_\mathrm{cod}}]/\mathcal{I}(Y) = \bar k[Y]$. -/
noncomputable def dominantPullbackToFractionRing
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y) :
    AffineCoordinateRingBar Y →+* FractionRing (AffineCoordinateRingBar X) :=
  Ideal.Quotient.lift (idealOfAlgebraicSet Y)
    (dominantPullbackSubstHom φ.components)
    (dominantPullbackSubstHom_kills_ideal φ)

end Theorem158
