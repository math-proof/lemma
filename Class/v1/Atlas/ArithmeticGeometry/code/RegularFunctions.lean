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
import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part4
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

/-- Each coordinate $\varphi_i = \varphi^*(Y_i)$ lies in $\bar k[X] \subseteq \bar k(X)$,
viewed via the substitution homomorphism. (This is the form needed for the pullback to
descend to coordinate rings; the proof uses regularity of the rational map.) -/
class of a constant polynomial $C(r)$ in $\bar k[Y]$ to the class of $C(r)$ in $\bar k[X]$.
This is the coordinate-ring version of `IsKbarFunctionFieldHom` for $\varphi^*$. -/

end Theorem158
