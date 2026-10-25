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
import Structure.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part2
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Corollary159

variable (k : Type*) [Field k]

open MvPolynomial CategoryTheory

attribute [instance] AffineVarietyDom.isDomain

/-- The identity rational map on $V$: defined as the rational map induced by the
identity ring homomorphism on $\bar k(V)$, which is a $\bar k$-algebra homomorphism. -/
noncomputable def AffineVarietyDom.idMap
    {k : Type*} [Field k]
    (V : AffineVarietyDom k) :
    @AffineRationalMap k _ V.dim V.dim V.carrier V.carrier V.isDomain :=
  @functionFieldMorphismInducedMap k _ V.dim V.dim V.carrier V.carrier V.isDomain V.isDomain
    (RingHom.id _) (fun _ => rfl) V.isAlgebraic

end Corollary159
