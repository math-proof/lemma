/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
import Def.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.ODE.PicardLindelof
import Structure.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- Cartan's magic formula applied to a chosen "scaling" vector field $V$:
$d\iota_V \beta + \iota_V d\beta = \mathcal{L}_V \beta$. -/
theorem cartan_for_scaling_field
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (V : VF) {p : ℕ} (β : Ω (p + 1)) :
    inst.d (inst.ι V β) + inst.ι V (inst.d β) = inst.L V β := by
  rw [cartan_formula]

/-- Derivation of the chain homotopy formula $dK + Kd = \mathrm{id} - \pi^* i^*$ from
Cartan's formula together with a "fundamental theorem of calculus" identity
$\Phi(\mathcal{L}_V \beta) = \beta - \pi^*(i^*\beta)$, where $K := \Phi \circ \iota_V$. -/
theorem homotopy_formula_from_cartan_and_ftc
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Ω_X : ℕ → Type*} {VF_X : Type*} [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF)
    (π : DFSMorphism Ω VF Ω_X VF_X)
    (V : VF) (Φ : ∀ {p : ℕ}, Ω p → Ω p) (K : ∀ {p : ℕ}, Ω (p + 1) → Ω p)

    (hK_def : ∀ {p : ℕ} (β : Ω (p + 1)), K β = Φ (inst.ι V β))

    (hΦ_add : ∀ {p : ℕ} (γ₁ γ₂ : Ω p), Φ (γ₁ + γ₂) = Φ γ₁ + Φ γ₂)

    (hΦ_d : ∀ {p : ℕ} (γ : Ω p), inst.d (Φ γ) = Φ (inst.d γ))

    (hFTC : ∀ {p : ℕ} (β : Ω (p + 1)), Φ (inst.L V β) = β - π.pullback (i.pullback β))
    {p : ℕ} (β : Ω (p + 1)) :
    inst.d (K β) + K (inst.d β) = β - π.pullback (i.pullback β) := by

  rw [hK_def β]


  rw [hK_def (inst.d β)]


  rw [hΦ_d (inst.ι V β)]


  rw [← hΦ_add]


  rw [cartan_for_scaling_field V β]


  exact hFTC β

/-- $\mathbb{R}$-linearity of $K = \Phi \circ \iota_V$ in its argument, derived from the
linearity of $\iota_V$ and the scalar-multiplicativity of $\Phi$. -/
theorem K_smul_from_axioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (V : VF) (Φ : ∀ {p : ℕ}, Ω p → Ω p)

    (hΦ_smul : ∀ {p : ℕ} (r : ℝ) (γ : Ω p), Φ (r • γ) = r • Φ γ)
    {p : ℕ} (r : ℝ) (α : Ω (p + 1)) :
    Φ (inst.ι V (r • α)) = r • Φ (inst.ι V α) := by
  rw [inst.ι_smul]
  exact hΦ_smul r (inst.ι V α)

/-- $K\beta = \Phi(\iota_V \beta)$ pulls back to zero on $X$, since $\iota_V$ already does
and $\Phi$ preserves vanishing on $X$. -/
theorem K_vanishes_on_X_from_axioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Ω_X : ℕ → Type*} {VF_X : Type*} [_inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF)
    (V : VF) (Φ : ∀ {p : ℕ}, Ω p → Ω p)

    (hιV_vanish : ∀ {p : ℕ} (β : Ω (p + 1)), i.pullback (inst.ι V β) = 0)

    (hΦ_preserve : ∀ {p : ℕ} (γ : Ω p), i.pullback γ = 0 → i.pullback (Φ γ) = 0)
    {p : ℕ} (β : Ω (p + 1)) :
    i.pullback (Φ (inst.ι V β)) = 0 := by
  exact hΦ_preserve (inst.ι V β) (hιV_vanish β)


