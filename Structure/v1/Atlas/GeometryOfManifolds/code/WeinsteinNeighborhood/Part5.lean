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
import Def.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part5
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- A global Moser flow $\varphi_M : M \to M$ matching $\omega_1$ to $\omega_0$ and
fixing $X$ restricts to a local diffeomorphism between open neighborhoods
$U_0, U_1$ of $X$. -/
structure IsClosedSubmanifold
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    [DifferentialFormSpace Ω_M VF_M]
    [DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M) : Prop where
  pullback_surj : ∀ (p : ℕ) (α : Ω_X p), ∃ (β : Ω_M p), i.pullback β = α

/-- All the geometric data produced by combining the tubular neighborhood theorem with
the Lagrangian normal-bundle identification $NX \cong T^*X$: a common neighborhood $U$
of $X$ carrying two symplectic forms $\omega_0$ (from $T^*X$) and $\omega_1$ (from $M$)
that agree on $X$, together with the auxiliary inclusions and a $V$-side neighborhood
diffeomorphic to $U$ identifying $\omega_1$ with the symplectic form on $M$. -/
structure TubularNeighborhoodGeometricData
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

