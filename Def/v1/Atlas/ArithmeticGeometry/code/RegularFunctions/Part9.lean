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
import Instance.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part3
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Corollary159

variable (k : Type*) [Field k]

open MvPolynomial CategoryTheory

attribute [instance] AffineVarietyDom.isDomain

attribute [instance] FunctionFieldObj.fieldInst FunctionFieldObj.algInst

/-- If $\varphi : X \dashrightarrow Y$ and $\psi : Y \dashrightarrow X$ are dominant
rational maps whose composition $\psi \circ \varphi$ is the identity on its domain in
$X$, then the composition of their function-field pullbacks is the identity on $\bar k(X)$. -/
noncomputable def functionFieldIsoToAlgEquiv
    (F G : FunctionFieldObj k)
    (i : F ≅ G) :
    G.carrier ≃ₐ[AlgebraicClosure k] F.carrier :=
  AlgEquiv.ofAlgHom
    i.hom.toAlgHom
    i.inv.toAlgHom
    (by
      have h := i.hom_inv_id
      exact congr_arg FunctionFieldObj.Hom.toAlgHom h)
    (by
      have h := i.inv_hom_id
      exact congr_arg FunctionFieldObj.Hom.toAlgHom h)

/-- Inverse of `functionFieldIsoToAlgEquiv`: convert a $\bar k$-algebra isomorphism
of function fields to an isomorphism in `FunctionFieldObj`. -/
noncomputable def algEquivToFunctionFieldIso
    (F G : FunctionFieldObj k)
    (e : G.carrier ≃ₐ[AlgebraicClosure k] F.carrier) :
    F ≅ G where
  hom := ⟨e.toAlgHom⟩
  inv := ⟨e.symm.toAlgHom⟩
  hom_inv_id := by
    apply FunctionFieldObj.Hom.ext
    ext x
    show e (e.symm x) = x
    simp
  inv_hom_id := by
    apply FunctionFieldObj.Hom.ext
    ext x
    show e.symm (e x) = x
    simp

end Corollary159
