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
import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part2
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section RegularFunctions

variable {k}

variable {n : ℕ} {X : Set (Fin n → AlgebraicClosure k)}

variable [hdom : IsDomain (AffineCoordinateRingBar X)]

/-- Definition 15.4 (affine rational map). A *rational map* $\varphi : X \dashrightarrow Y$
between affine algebraic sets is a tuple of components $(\varphi_1, \dots, \varphi_{n_\mathrm{cod}})$
with each $\varphi_i \in \bar k(X)$, together with the requirement that whenever the tuple
is regular at $P \in X$, the resulting point $(\varphi_1(P), \dots, \varphi_{n_\mathrm{cod}}(P))$
lies in the target $Y$. -/
structure AffineRationalMap
    (X : Set (Fin m → AlgebraicClosure k))
    (Y : Set (Fin n_cod → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)] where
  components : Fin n_cod → FractionRing (AffineCoordinateRingBar X)
  image_mem : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt components P hP),
    evalTupleAt components P hP hreg ∈ Y

end RegularFunctions
