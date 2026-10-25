/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lattice
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
open Complex


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The weight-`k` Eisenstein series of a lattice `L`, defined as `G_k(L) = ∑' l∈L \{0},
1 / l^k`. Packaged as `L.G k` from `ComplexLattice`. -/
def eisensteinSeries (k : ℕ) : ℂ := L.G k

/-- The classical modular invariant `g₂(L)` equals `60` times the weight-4 Eisenstein
series `G_4(L)`. -/
def ofUpperHalfPlane (τ : UpperHalfPlane) : ComplexLattice :=
  ComplexLattice.mk' 1 (τ : ℂ) (by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    refine ⟨?_, ?_⟩
    · intro h
      have := τ.coe_im_pos
      simp [h] at this
    · intro a ha
      have him := τ.coe_im_pos
      have him2 : (a • (τ : ℂ)).im = (1 : ℂ).im := congr_arg Complex.im ha
      simp [Complex.one_im] at him2
      rcases him2 with ha0 | him0
      · rw [ha0] at ha; simp at ha
      · exact absurd him0 (ne_of_gt him))

end ComplexLattice

open scoped UpperHalfPlane

/-- The function `τ ↦ g₂(ℤ + ℤτ)` on the upper half-plane. -/
def discriminantFunction (τ : ℍ) : ℂ :=
  (ComplexLattice.ofUpperHalfPlane τ).discriminantLattice

/-- The modular `j`-function `j(τ) = 1728 g₂(τ)^3 / Δ(τ)` on the upper half-plane. -/
def jFunction (τ : ℍ) : ℂ :=
  (ComplexLattice.ofUpperHalfPlane τ).jInvariantLattice

section Theorem_15_8

open ComplexLattice Pointwise

/-- The translation `τ ↦ τ + 1` on the upper half-plane (it preserves the upper half-plane
because the imaginary part is unchanged). -/
def UpperHalfPlane.addOne (τ : ℍ) : ℍ :=
  ⟨(τ : ℂ) + 1, by
    simp only [Complex.add_im, Complex.one_im, add_zero]
    exact τ.2⟩

/-- The inversion `τ ↦ -1/τ` on the upper half-plane (preserves the upper half-plane
because `Im(-1/τ) = Im τ / |τ|² > 0`). -/
def UpperHalfPlane.negInv (τ : ℍ) : ℍ :=
  ⟨-(τ : ℂ)⁻¹, by
    have him := τ.2
    have hτne : (τ : ℂ) ≠ 0 := by
      intro h; rw [h] at him; simp at him
    simp only [Complex.neg_im, Complex.inv_im]
    have : -(-((τ : ℂ)).im / Complex.normSq (τ : ℂ)) =
        ((τ : ℂ)).im / Complex.normSq (τ : ℂ) := by ring
    rw [this]
    exact div_pos him (Complex.normSq_pos.mpr hτne)⟩

end Theorem_15_8
end
