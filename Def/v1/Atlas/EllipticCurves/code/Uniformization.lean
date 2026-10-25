/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Uniformization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.EisensteinSeries
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EisensteinSeries
import Lemma.Complex.Atlas.v1.EllipticCurves.code.JInvariant
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.WeierstrassPOrder
import Def.v1.Atlas.EllipticCurves.code.JInvariant
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Theorem.v1.Atlas.EllipticCurves.code.WeierstrassPOrder
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Modular
open Complex PeriodPair


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- If `℘(z) = ℘(w)` for nonlattice `z, w` with `2w ∈ L`, then `z - w ∈ L`.
This combines `weierstrassP_eq_implies_pm` with the assumption that `w` is a
half period. -/
def ellipticCurveOfLattice : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -(L.g₂ / 4), -(L.g₃ / 4)⟩

/-- Two lattices `L, L'` are said to give *isomorphic elliptic curves over* ℂ
if there is a Weierstrass variable change taking `E_L` to `E_{L'}`. -/
def EllipticCurveIsomorphicOverC (L L' : ComplexLattice) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange ℂ,
    C • L.ellipticCurveOfLattice = L'.ellipticCurveOfLattice

/-- The standard (closed) fundamental domain for the action of `SL(2, ℤ)` on
the upper half plane, as defined in mathlib via `ModularGroup.fd`. -/
def standardFundamentalDomain : Set ℍ := ModularGroup.fd

/-- The open standard fundamental domain `fdo` for the action of `SL(2, ℤ)` on
`ℍ`. -/
def standardOpenFundamentalDomain : Set ℍ := ModularGroup.fdo

/-- The textbook (half-open) fundamental domain of Lemma 15.10:
`{τ ∈ ℍ : -1/2 ≤ Re τ < 1/2, |τ| ≥ 1, and |τ| > 1 if Re τ > 0}`. -/
def bookFundamentalDomain : Set ℍ :=
  {τ | (-1/2 : ℝ) ≤ τ.re ∧ τ.re < 1/2 ∧ 1 ≤ Complex.normSq (τ : ℂ) ∧
       (0 < τ.re → 1 < Complex.normSq (τ : ℂ))}

/-- Uniformization up to isomorphism: every elliptic curve `y² = x³ + A x + B`
over ℂ is isomorphic, via a Weierstrass variable change, to the curve
`y² = x³ - (g₂/4) x - (g₃/4)` of some lattice `L`. -/
def scaleLattice (c : ℂ) (hc : c ≠ 0) (L : ComplexLattice) : ComplexLattice :=
  ComplexLattice.mk' (c * L.ω₁) (c * L.ω₂) (by
    have hL := L.linearIndependent
    rw [linearIndependent_fin2] at hL ⊢
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hL ⊢
    constructor
    · intro h
      have : c * L.ω₂ = 0 := h
      rcases mul_eq_zero.mp this with hc0 | hω2
      · exact absurd hc0 hc
      · exact absurd hω2 hL.1
    · intro a ha
      apply hL.2 a
      have h1 : a • (c * L.ω₂) = c * L.ω₁ := ha
      have h2 : c * (a • L.ω₂) = c * L.ω₁ := by
        rw [mul_smul_comm]; exact h1
      exact mul_left_cancel₀ hc h2)


/-- Equivalence between the scaled lattice `scaleLattice c hc L` and `L`,
implemented as multiplication by `c⁻¹`/`c`. -/
def scaleLatticeEquiv (c : ℂ) (hc : c ≠ 0) (L : ComplexLattice) :
    (scaleLattice c hc L).lattice ≃ L.lattice where
  toFun l := ⟨c⁻¹ * (l : ℂ), by
    have hl := l.2
    rw [ComplexLattice.mem_lattice_iff] at hl ⊢
    obtain ⟨n₁, n₂, hl⟩ := hl
    exact ⟨n₁, n₂, by
      simp only [scaleLattice, ComplexLattice.mk'] at hl
      rw [← hl]; field_simp⟩⟩

  invFun l := ⟨c * (l : ℂ), by
    have hl := l.2
    rw [ComplexLattice.mem_lattice_iff] at hl ⊢
    obtain ⟨n₁, n₂, hl⟩ := hl
    exact ⟨n₁, n₂, by
      simp only [scaleLattice, ComplexLattice.mk']
      rw [← hl]; ring⟩⟩
  left_inv l := Subtype.ext (by field_simp)
  right_inv l := Subtype.ext (by field_simp)

end ComplexLattice
end
