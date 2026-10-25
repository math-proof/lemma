/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.EllipticFunction.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EllipticFunction
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Theorem161
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Structure.v1.Atlas.EllipticCurves.code.Theorem161
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part2


namespace ComplexLattice

noncomputable section

open Pointwise

/-- Reflexivity of ideal equivalence: every lattice is equivalent to itself (witnessed
by $\alpha = \beta = 1$). -/
theorem IsEquivalent.refl (𝒪 : Subring ℂ) (L : ComplexLattice) : IsEquivalent 𝒪 L L :=
  ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩

/-- Symmetry of ideal equivalence: if $\alpha L_1 = \beta L_2$, then $\beta L_2 =
\alpha L_1$ (with the roles of $\alpha$ and $\beta$ swapped). -/
theorem IsEquivalent.symm {𝒪 : Subring ℂ} {L₁ L₂ : ComplexLattice}
    (h : IsEquivalent 𝒪 L₁ L₂) : IsEquivalent 𝒪 L₂ L₁ := by
  obtain ⟨α, β, hα, hβ, h⟩ := h
  exact ⟨β, α, hβ, hα, h.symm⟩

/-- Transitivity of ideal equivalence: if $\alpha_1 L_1 = \beta_1 L_2$ and
$\alpha_2 L_2 = \beta_2 L_3$, then $(\alpha_2\alpha_1) L_1 = (\beta_1\beta_2) L_3$. -/
theorem IsEquivalent.trans {𝒪 : Subring ℂ} {L₁ L₂ L₃ : ComplexLattice}
    (h₁₂ : IsEquivalent 𝒪 L₁ L₂) (h₂₃ : IsEquivalent 𝒪 L₂ L₃) :
    IsEquivalent 𝒪 L₁ L₃ := by
  obtain ⟨α₁, β₁, hα₁, hβ₁, h₁⟩ := h₁₂
  obtain ⟨α₂, β₂, hα₂, hβ₂, h₂⟩ := h₂₃
  refine ⟨α₂ * α₁, β₁ * β₂, ?_, ?_, ?_⟩
  · simp only [Subring.coe_mul]; exact mul_ne_zero hα₂ hα₁
  · simp only [Subring.coe_mul]; exact mul_ne_zero hβ₁ hβ₂
  · simp only [Subring.coe_mul, ← smul_smul]
    calc (↑α₂ : ℂ) • (↑α₁ : ℂ) • (L₁.lattice : Set ℂ)
        = (↑α₂ : ℂ) • (↑β₁ : ℂ) • (L₂.lattice : Set ℂ) := by rw [h₁]
      _ = (↑β₁ : ℂ) • (↑α₂ : ℂ) • (L₂.lattice : Set ℂ) := by
          rw [show (↑α₂ : ℂ) • (↑β₁ : ℂ) • (L₂.lattice : Set ℂ) =
                  (↑β₁ : ℂ) • (↑α₂ : ℂ) • (L₂.lattice : Set ℂ) from by
            rw [smul_smul, smul_smul, mul_comm]]
      _ = (↑β₁ : ℂ) • (↑β₂ : ℂ) • (L₃.lattice : Set ℂ) := by rw [h₂]

/-- The relation `IsEquivalent 𝒪` is an equivalence relation on complex lattices. -/
theorem isEquivalent_equivalence (𝒪 : Subring ℂ) :
    Equivalence (IsEquivalent 𝒪) :=
  ⟨IsEquivalent.refl 𝒪, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Ideal equivalence implies homothety: if $\alpha L_1 = \beta L_2$, then
$L_2 = (\beta^{-1}\alpha) L_1$, so the lattices are homothetic with factor
$\beta^{-1}\alpha$. -/
theorem IsEquivalent.isHomothetic {𝒪 : Subring ℂ} {L₁ L₂ : ComplexLattice}
    (h : IsEquivalent 𝒪 L₁ L₂) : IsHomothetic L₁ L₂ := by
  obtain ⟨α, β, hα, hβ, h⟩ := h
  refine ⟨(β : ℂ)⁻¹ * (α : ℂ), mul_ne_zero (inv_ne_zero hβ) hα, ?_⟩

  have := congr_arg ((β : ℂ)⁻¹ • ·) h
  simp only [smul_smul, inv_mul_cancel₀ hβ, one_smul] at this
  exact this.symm

end
end ComplexLattice
