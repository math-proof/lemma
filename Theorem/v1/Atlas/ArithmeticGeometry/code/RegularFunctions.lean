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
import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Evaluation

/-- Compatibility of `evalBarAtPoint` with the quotient map: evaluating the class of a
polynomial $f$ at $P$ equals the ordinary polynomial evaluation $f(P)$. -/
@[simp]
theorem evalBarAtPoint_mk {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (f : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    evalBarAtPoint k X P hP (Ideal.Quotient.mk _ f) = eval P f :=
  Ideal.Quotient.lift_mk _ _ _

end Evaluation
