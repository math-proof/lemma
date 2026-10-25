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
import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part6
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

/-- The composite $k[X] \to \bar k[X] \hookrightarrow \bar k(X)$ is injective. Needed to
extend the scalar-extension map to the level of function fields. -/
theorem coordRingToBar_comp_algebraMap_injective
    {k : Type*} [Field k]
    {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRing X)] :
    Function.Injective
      ((algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))).comp
        (coordRingToBar X)) :=
  (IsFractionRing.injective (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))).comp (fun a b hab => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hab' : Ideal.Quotient.mk (idealOfAlgebraicSet X)
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) a) =
      Ideal.Quotient.mk (idealOfAlgebraicSet X)
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) b) := by
      change coordRingToBar X (Ideal.Quotient.mk (idealOverK X) a) =
        coordRingToBar X (Ideal.Quotient.mk (idealOverK X) b) at hab
      simp only [coordRingToBar] at hab
      exact hab
    rw [Ideal.Quotient.eq] at hab'
    have hmem : a - b ∈ idealOverK X :=
      mem_idealOverK_iff.mpr (by rwa [map_sub])
    exact Ideal.Quotient.eq.mpr hmem)

end Theorem158
