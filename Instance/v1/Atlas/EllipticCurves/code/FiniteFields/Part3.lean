/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Theorem.v1.Atlas.EllipticCurves.code.FiniteFields.Part4


section Theorem_3_15

open Polynomial IntermediateField

/-- The set of primitive polynomials of degree `n` in `𝔽_p[x]` is finite: a
primitive polynomial of degree `n` is determined by its `n` lower coefficients
in `𝔽_p`, of which there are finitely many. -/
instance finite_primitivePolys (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    Finite {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n} := by
  apply Finite.of_injective
    (fun (⟨f, ⟨hm, _, _⟩, _⟩ :
      {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n}) =>
      (fun (i : Fin n) => f.coeff i.val : Fin n → ZMod p))
  intro ⟨f, ⟨hfm, _, _⟩, hfn⟩ ⟨g, ⟨hgm, _, _⟩, hgn⟩ h
  simp only [Subtype.mk.injEq]; ext i
  by_cases hi : i < n
  · exact congr_fun h ⟨i, hi⟩
  · by_cases hi2 : i = n
    · have h1 : f.coeff i = 1 := by rw [hi2, ← hfn]; exact hfm.leadingCoeff
      have h2 : g.coeff i = 1 := by rw [hi2, ← hgn]; exact hgm.leadingCoeff
      rw [h1, h2]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < i)]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < i)]

end Theorem_3_15
