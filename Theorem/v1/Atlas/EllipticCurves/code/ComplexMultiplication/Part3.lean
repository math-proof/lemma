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
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part3


namespace ComplexLattice

noncomputable section

open Pointwise

/-- A proper $\mathcal{O}$-ideal is contained in $\mathcal{O}$: every element of the
lattice underlying a proper ideal lies in $\mathcal{O}$. -/
theorem lattice_subset_of_isImagQuadOrder (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪) (L : ProperIdeal 𝒪)
    (z : ℂ) (hz : z ∈ L.val.toAddSubgroup) : z ∈ 𝒪 :=
  L.property.2 z hz

/-- The first basis vector $\omega_1$ of a proper $\mathcal{O}$-ideal lies in
$\mathcal{O}$. -/
theorem omega1_mem_of_isImagQuadOrder (𝒪 : Subring ℂ) (h𝒪 : IsImagQuadOrder 𝒪)
    (L : ProperIdeal 𝒪) : L.val.ω₁ ∈ 𝒪 :=
  lattice_subset_of_isImagQuadOrder 𝒪 h𝒪 L L.val.ω₁ (ComplexLattice.ω₁_mem L.val)

/-- If $L_2 = c \cdot L_1$ (homothety) with $c \neq 0$ and both are proper
$\mathcal{O}$-ideals, then $c \omega_1(L_1) \in \mathcal{O}$. -/
theorem lambda_omega1_mem_of_isImagQuadOrder (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪)
    (L₁ L₂ : ProperIdeal 𝒪) (c : ℂ) (hc : c ≠ 0)
    (hL : (L₂.val.lattice : Set ℂ) = c • (L₁.val.lattice : Set ℂ)) :
    c * L₁.val.ω₁ ∈ 𝒪 := by
  have hω₁_in_L₁ : L₁.val.ω₁ ∈ (L₁.val.lattice : Set ℂ) := ComplexLattice.ω₁_mem L₁.val
  have hcω₁_in_L₂ : c * L₁.val.ω₁ ∈ (L₂.val.lattice : Set ℂ) := by
    rw [hL]; exact ⟨L₁.val.ω₁, hω₁_in_L₁, rfl⟩
  exact lattice_subset_of_isImagQuadOrder 𝒪 h𝒪 L₂ (c * L₁.val.ω₁) hcω₁_in_L₂

/-- For proper ideals of an imaginary-quadratic order, homothety implies ideal
equivalence.  Combined with the converse `IsEquivalent.isHomothetic`, this means
the two notions of equivalence coincide for proper ideals. -/
theorem isEquivalent_of_isHomothetic_properIdeal (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪) (L₁ L₂ : ProperIdeal 𝒪)
    (h : IsHomothetic L₁.val L₂.val) : IsEquivalent 𝒪 L₁.val L₂.val := by
  obtain ⟨c, hc_ne, hL2_eq⟩ := h
  have hω₁_mem : L₁.val.ω₁ ∈ 𝒪 := omega1_mem_of_isImagQuadOrder 𝒪 h𝒪 L₁
  have hcω₁_mem : c * L₁.val.ω₁ ∈ 𝒪 :=
    lambda_omega1_mem_of_isImagQuadOrder 𝒪 h𝒪 L₁ L₂ c hc_ne hL2_eq
  have hω₁_ne : L₁.val.ω₁ ≠ 0 := by
    have h0 := L₁.val.indep.ne_zero (0 : Fin 2)
    simp only [Matrix.cons_val_zero] at h0
    exact h0
  refine ⟨⟨c * L₁.val.ω₁, hcω₁_mem⟩, ⟨L₁.val.ω₁, hω₁_mem⟩, ?_, ?_, ?_⟩
  · exact mul_ne_zero hc_ne hω₁_ne
  · exact hω₁_ne
  · show (c * L₁.val.ω₁) • (L₁.val.lattice : Set ℂ) =
         L₁.val.ω₁ • (L₂.val.lattice : Set ℂ)
    rw [hL2_eq, smul_smul]
    congr 1
    ring

/-- For proper ideals of an order in an imaginary quadratic field, ideal equivalence
and homothety are equivalent notions. -/
theorem isEquivalent_iff_isHomothetic_properIdeal (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪) (L₁ L₂ : ProperIdeal 𝒪) :
    IsEquivalent 𝒪 L₁.val L₂.val ↔ IsHomothetic L₁.val L₂.val :=
  ⟨IsEquivalent.isHomothetic, isEquivalent_of_isHomothetic_properIdeal 𝒪 h𝒪 L₁ L₂⟩

end
end ComplexLattice
