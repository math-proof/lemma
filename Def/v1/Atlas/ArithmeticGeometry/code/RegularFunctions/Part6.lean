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
import Theorem.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part3
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

/-- The *rational map induced* by a $\bar k$-algebra homomorphism $\theta : \bar k(Y) \to
\bar k(X)$: its components are $\theta(Y_1), \dots, \theta(Y_{n_\mathrm{cod}})$, and the
image-membership condition is provided by `functionFieldMorphism_image_mem`. This is the
construction of Theorem 15.8(iii) producing $\varphi$ from $\theta$. -/
noncomputable def functionFieldMorphismInducedMap {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (hY : IsAlgebraicSubset k n_cod Y) :
    AffineRationalMap X Y where
  components := functionFieldMorphismComponents θ
  image_mem := functionFieldMorphism_image_mem θ hθ hY

/-- The natural ring homomorphism $k[X] \to \bar k[X]$ extending scalars from the base
field $k$ to its algebraic closure $\bar k$: descends the map induced on polynomials by
$k \hookrightarrow \bar k$ to the quotient defining $k[X]$. -/
noncomputable def coordRingToBar {n : ℕ}
    (X : Set (Fin n → AlgebraicClosure k)) :
    AffineCoordinateRing X →+* AffineCoordinateRingBar X :=
  Ideal.Quotient.lift (idealOverK X)
    ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp
      (MvPolynomial.map (algebraMap k (AlgebraicClosure k))))
    (fun f hf => by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_idealOverK_iff.mp hf))

end Theorem158
