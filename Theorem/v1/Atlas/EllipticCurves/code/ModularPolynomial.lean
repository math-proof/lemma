/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.CharP.Defs
import Def.v1.Atlas.EllipticCurves.code.ModularCurves.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ModularCurves
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Def.v1.Atlas.EllipticCurves.code.ModularPolynomial.Part2
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup Complex


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
