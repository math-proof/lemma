/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticStandardBasis
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticEvenDim
import Theorem.v1.Atlas.GeometryOfManifolds.code.SymplecticStandardBasis
import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
import Def.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
set_option autoImplicit false

universe u_chart v_chart

open Module FiniteDimensional Finset
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- Axiomatized chart existence: every symplectic manifold admits a Euclidean-type chart
$(\Omega', VF')$ with finite-dimensional contraction together with a symplectic form
$\tilde\omega$ pulling back via the chart morphism to $S.\omega$. -/
structure HasMoserFlowData
    {Ω_M : ℕ → Type u_M} {VF_M : Type v_M}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    {Ω_X : ℕ → Type u_X} {VF_X : Type v_X}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (ω₀ ω₁ : Ω_M 2) where
  Ω_U₀ : ℕ → Type u_M
  VF_U₀ : Type v_M
  inst_U₀ : DifferentialFormSpace Ω_U₀ VF_U₀
  incl₀ : @DFSMorphism Ω_U₀ VF_U₀ Ω_M VF_M inst_U₀ inst_M
  i_X_U₀ : @DFSMorphism Ω_X VF_X Ω_U₀ VF_U₀ inst_X inst_U₀
  Ω_U₁ : ℕ → Type u_M
  VF_U₁ : Type v_M
  inst_U₁ : DifferentialFormSpace Ω_U₁ VF_U₁
  incl₁ : @DFSMorphism Ω_U₁ VF_U₁ Ω_M VF_M inst_U₁ inst_M
  i_X_U₁ : @DFSMorphism Ω_X VF_X Ω_U₁ VF_U₁ inst_X inst_U₁
  φ : @DFSMorphism Ω_U₀ VF_U₀ Ω_U₁ VF_U₁ inst_U₀ inst_U₁
  φ_inv : @DFSMorphism Ω_U₁ VF_U₁ Ω_U₀ VF_U₀ inst_U₁ inst_U₀
  compat₀ : ∀ {p : ℕ} (α : Ω_M p), i_X_U₀.pullback (incl₀.pullback α) = i.pullback α
  compat₁ : ∀ {p : ℕ} (α : Ω_M p), i_X_U₁.pullback (incl₁.pullback α) = i.pullback α
  pullback_eq : φ.pullback (incl₁.pullback ω₁) = incl₀.pullback ω₀
  φ_identity_on_X : ∀ {p : ℕ} (α : Ω_U₁ p),
      i_X_U₀.pullback (φ.pullback α) = i_X_U₁.pullback α
  φ_inv_left : ∀ {p : ℕ} (α : Ω_U₁ p),
      φ_inv.pullback (φ.pullback α) = α
  φ_inv_right : ∀ {p : ℕ} (α : Ω_U₀ p),
      φ.pullback (φ_inv.pullback α) = α
  φ_inv_identity_on_X : ∀ {p : ℕ} (α : Ω_U₀ p),
      i_X_U₁.pullback (φ_inv.pullback α) = i_X_U₀.pullback α

