/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutMultiplicitySum
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal
open MvPolynomial Classical


noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- Translation of polynomials by a fixed point is an injective operation, since translating by
`-p` is a left inverse. -/
lemma translatePoly_injective {n : ℕ} (p : Fin n → k) :
    Function.Injective (fun g => translatePoly k g p) := by
  suffices h : ∀ g : MvPolynomial (Fin n) k,
      translatePoly k (translatePoly k g p) (fun i => -p i) = g by
    exact Function.HasLeftInverse.injective
      ⟨fun g => translatePoly k g (fun i => -p i), h⟩
  intro g
  simp only [translatePoly]
  conv_rhs => rw [← AlgHom.id_apply (R := k) g]
  rw [← AlgHom.comp_apply]
  congr 1; ext i; simp [map_add, map_neg]

/-- Translating a nonzero polynomial yields a nonzero polynomial. -/
lemma translatePoly_ne_zero {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k)
    (hg : g ≠ 0) : translatePoly k g p ≠ 0 := by
  intro heq; apply hg
  have hinj := translatePoly_injective k p
  have h0 : translatePoly k (0 : MvPolynomial (Fin n) k) p = 0 := by
    simp [translatePoly, map_zero]
  have : (fun g => translatePoly k g p) g = (fun g => translatePoly k g p) 0 := by
    simp only; rw [heq, h0]
  exact hinj this

/-- A nonzero polynomial has a nonzero homogeneous component of some degree. -/
lemma exists_homogeneousComponent_ne_zero {n : ℕ}
    (φ : MvPolynomial (Fin n) k) (h : φ ≠ 0) :
    ∃ m : ℕ, MvPolynomial.homogeneousComponent m φ ≠ 0 := by
  by_contra hall; push Not at hall; apply h
  have := MvPolynomial.sum_homogeneousComponent φ
  simp only [hall, Finset.sum_const_zero] at this; exact this.symm

end Lec5BezoutPascal
end
