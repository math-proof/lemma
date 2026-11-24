module
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Algebra.CharP.Defs
public import Def.v1.Atlas.EllipticCurves.code.ModularCurves.Part3
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.ModularCurves
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Uniformization
public import Def.v1.Atlas.EllipticCurves.code.Uniformization
public import Def.v1.Atlas.EllipticCurves.code.ModularPolynomial.Part2
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup Complex


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open ModularFunction

section ModularCurveX0Defs

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups UpperHalfPlane

/-- The determinant identity `ad - bc = 1` rewritten in terms of `sl2zEntry`. -/
lemma sl2zEntry_det (γ : SL(2, ℤ)) :
    sl2zEntry γ 0 0 * sl2zEntry γ 1 1 - sl2zEntry γ 0 1 * sl2zEntry γ 1 0 = 1 := by
  simp only [sl2zEntry]
  have hd := γ.det_coe
  rw [det_fin_two] at hd
  exact_mod_cast hd

/-- The matrix-product entry formula `(g₁ g₂)_{ij} = g₁_{i0} g₂_{0j} + g₁_{i1} g₂_{1j}`
for `SL₂(ℤ)`-matrices, expressed via `sl2zEntry`. -/
lemma sl2zEntry_mul (g₁ g₂ : SL(2, ℤ)) (i j : Fin 2) :
    sl2zEntry (g₁ * g₂) i j =
    sl2zEntry g₁ i 0 * sl2zEntry g₂ 0 j + sl2zEntry g₁ i 1 * sl2zEntry g₂ 1 j := by
  simp only [sl2zEntry]
  simp [mul_apply, Fin.sum_univ_two]

end ModularCurveX0Defs
end
