module
public import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Opposites
public import Structure.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part4
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


section Corollary159

variable (k : Type*) [Field k]

open MvPolynomial CategoryTheory

attribute [instance] AffineVarietyDom.isDomain

attribute [instance] FunctionFieldObj.fieldInst FunctionFieldObj.algInst

/-- Category structure on `FunctionFieldObj k`: objects are finitely generated function
fields over $\bar k$ and morphisms are $\bar k$-algebra homomorphisms in the reversed
direction (so the resulting equivalence with `AffineVarietyDom` is covariant in this
formalisation). -/
noncomputable instance : Category (FunctionFieldObj k) where
  Hom F G := FunctionFieldObj.Hom k F G
  id F := ⟨AlgHom.id (AlgebraicClosure k) F.carrier⟩
  comp f g := ⟨f.toAlgHom.comp g.toAlgHom⟩

end Corollary159
