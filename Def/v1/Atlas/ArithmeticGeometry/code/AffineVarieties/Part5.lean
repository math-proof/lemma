/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Nullstellensatz
import Theorem.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part3
variable (k : Type*) [Field k]


section Corollary1218

open MvPolynomial

variable {n : ℕ}

/-- Corollary 12.18: the Nullstellensatz bijection between radical ideals of
$\overline{k}[x_1, \ldots, x_n]$ and algebraic subsets of $\overline{k}^n$. -/
noncomputable def radicalIdealAlgebraicSetEquiv :
    {I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k)) // I.IsRadical} ≃
    {V : Set (AffineSpace_k k n) // IsAlgebraicSubset k n V} where
  toFun I :=
    let S : Set (MvPolynomial (Fin n) (AlgebraicClosure k)) := I.1
    ⟨AlgebraicSet k n S, S, rfl⟩
  invFun V := ⟨idealOfAlgebraicSet V.1, idealOfAlgebraicSet_isRadical k V.1⟩
  left_inv := fun ⟨I, hI⟩ => by
    simp only
    ext1
    exact idealOfAlgebraicSet_algebraicSet_of_isRadical k I hI
  right_inv := fun ⟨V, hV⟩ => by
    simp only
    ext1
    exact algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV


end Corollary1218
