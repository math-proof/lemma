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
import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part7
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Corollary159

variable (k : Type*) [Field k]

open MvPolynomial CategoryTheory

/-- The $\bar k$-algebra structure on $\bar k[Z]$ obtained from the natural map
$\bar k \hookrightarrow \bar k[x_1, \dots, x_n]$ followed by the quotient. -/
noncomputable instance instAlgebraAffineCoordinateRingBar {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :
    Algebra (AlgebraicClosure k) (AffineCoordinateRingBar Z) :=
  show Algebra (AlgebraicClosure k)
    (MvPolynomial (Fin n) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet Z) from
    Ideal.Quotient.algebra (AlgebraicClosure k)

end Corollary159
