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
import Structure.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part5
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- Axiomatic existence of `TubularNeighborhoodGeometricData` for any closed
Lagrangian submanifold $X$ of a symplectic manifold $(M, \omega)$. -/
class HasMoserInfrastructure
    {Ω : ℕ → Type u_Ω} {VF : Type u_VF}
    [inst : DifferentialFormSpace Ω VF]
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF) where
  homotopyPrimitives : HasTubularHomotopyPrimitives Ω VF Ω_X VF_X i
  moserTransportData :
    (ω₀ ω₁ : Ω 2) →
    (hclosed₀ : inst.d ω₀ = 0) → (hclosed₁ : inst.d ω₁ = 0) →
    (hnd₀ : Function.Injective (fun X => inst.ι X ω₀)) →
    (hagree : ∀ (V : VF), i.pullback (inst.ι V ω₀) = i.pullback (inst.ι V ω₁)) →
    (hH : HasRelativeHomotopyOperator Ω VF Ω_X VF_X i) →
    ∃ (φ : DFSMorphism Ω VF Ω VF) (φ_inv : DFSMorphism Ω VF Ω VF),
      φ.pullback ω₁ = ω₀ ∧
      (∀ {p : ℕ} (α : Ω p), φ_inv.pullback (φ.pullback α) = α) ∧
      (∀ {p : ℕ} (α : Ω p), φ.pullback (φ_inv.pullback α) = α) ∧
      (∀ {p : ℕ} (α : Ω p), i.pullback (φ.pullback α) = i.pullback α)


/-- All the geometric and Moser-flow data needed to prove Weinstein's Lagrangian
neighborhood theorem: a common neighborhood $U$ of $X$ with two symplectic forms
$\omega_0$ (induced from $T^*X$) and $\omega_1$ (induced from $M$), a $V$-side
neighborhood diffeomorphic to $U$ realizing $\omega_1$ as a pullback of the symplectic
form on $M$, and a Moser flow $\varphi$ on $U$ matching $\omega_1$ to $\omega_0$
that fixes $X$. -/
class HasLagrangianTubularData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_TX : ℕ → Type*} {VF_TX : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_TX : DifferentialFormSpace Ω_TX VF_TX]
    [hCot : CotangentBundleDFS Ω_X VF_X Ω_TX VF_TX]
    (S_M : SymplecticManifold Ω_M VF_M)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (hLag : IsLagrangianSubmanifold S_M i (2 * hCot.dimX) hCot.dimX) where
  Ω_U : ℕ → Type*
  VF_U : Type*
  inst_U : DifferentialFormSpace Ω_U VF_U
  j : @DFSMorphism Ω_X VF_X Ω_U VF_U inst_X inst_U
  ω₀ : Ω_U 2
  ω₁ : Ω_U 2
  hclosed₀ : inst_U.d ω₀ = 0
  hclosed₁ : inst_U.d ω₁ = 0
  hagree : ∀ (V : VF_U), j.pullback (inst_U.ι V ω₀) = j.pullback (inst_U.ι V ω₁)
  hnd₀ : Function.Injective (fun (X : VF_U) => inst_U.ι X ω₀)
  hnd₁ : Function.Injective (fun (X : VF_U) => inst_U.ι X ω₁)
  Ω_V : ℕ → Type*
  VF_V : Type*
  inst_V : DifferentialFormSpace Ω_V VF_V
  ψ : @DFSMorphism Ω_U VF_U Ω_V VF_V inst_U inst_V
  ψ_inv : @DFSMorphism Ω_V VF_V Ω_U VF_U inst_V inst_U
  S_V : @SymplecticManifold Ω_V VF_V inst_V
  j_V : @DFSMorphism Ω_X VF_X Ω_V VF_V inst_X inst_V
  ψ_left : ∀ {p : ℕ} (α : Ω_V p), ψ_inv.pullback (ψ.pullback α) = α
  ψ_right : ∀ {p : ℕ} (α : Ω_U p), ψ.pullback (ψ_inv.pullback α) = α
  hω₁ : ψ.pullback S_V.ω = ω₁
  hψ_X : ∀ {p : ℕ} (α : Ω_V p), j.pullback (ψ.pullback α) = j_V.pullback α
  ι_U : @DFSMorphism Ω_U VF_U Ω_TX VF_TX inst_U inst_TX
  ι_V : @DFSMorphism Ω_V VF_V Ω_M VF_M inst_V inst_M
  hι_U_compat : ∀ {p : ℕ} (α : Ω_TX p), j.pullback (ι_U.pullback α) = hCot.zeroSection.pullback α
  hι_V_compat : ∀ {p : ℕ} (α : Ω_M p), j_V.pullback (ι_V.pullback α) = i.pullback α

  φ : @DFSMorphism Ω_U VF_U Ω_U VF_U inst_U inst_U
  φ_inv : @DFSMorphism Ω_U VF_U Ω_U VF_U inst_U inst_U
  hφ_pull : φ.pullback ω₁ = ω₀
  hφ_left : ∀ {p : ℕ} (α : Ω_U p), φ_inv.pullback (φ.pullback α) = α
  hφ_right : ∀ {p : ℕ} (α : Ω_U p), φ.pullback (φ_inv.pullback α) = α
  hφ_id_X : ∀ {p : ℕ} (α : Ω_U p), j.pullback (φ.pullback α) = j.pullback α

