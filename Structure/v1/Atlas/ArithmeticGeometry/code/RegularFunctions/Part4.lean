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
import Instance.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part2
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Corollary159

variable (k : Type*) [Field k]

open MvPolynomial CategoryTheory

attribute [instance] AffineVarietyDom.isDomain

attribute [instance] FunctionFieldObj.fieldInst FunctionFieldObj.algInst

/-- A morphism $F \to G$ in the category of function fields is a $\bar k$-algebra
homomorphism $G \to F$ on the underlying fields (note the direction: the category is
contravariant relative to the algebra-homomorphism direction). -/
@[ext]
structure FunctionFieldObj.Hom (F G : FunctionFieldObj k) where
  toAlgHom : G.carrier →ₐ[AlgebraicClosure k] F.carrier

end Corollary159
