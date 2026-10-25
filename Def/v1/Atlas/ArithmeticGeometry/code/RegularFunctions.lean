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
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Evaluation

/-- Evaluation of an element of the $\bar k$-coordinate ring $\bar k[X]$ at a point $P \in X$.
Given a class $[f] \in \bar k[X] = \bar k[X_1, \dots, X_n]/I(X)$ and a point $P \in X$, this
yields $f(P) \in \bar k$. Well-defined because $I(X)$ vanishes on $X$. -/
noncomputable def evalBarAtPoint {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X) :
    AffineCoordinateRingBar X →+* AlgebraicClosure k :=
  Ideal.Quotient.lift (idealOfAlgebraicSet X) (eval P) (fun _f hf => hf P hP)

end Evaluation
