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
import Structure.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part3
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- The data of an *exponential map* used in proving the tubular neighborhood theorem:
an open neighborhood $U_0$ of $X$ in $NX$ together with a smooth map
$\exp : U_0 \to M$ whose restriction to the zero section is $i : X \hookrightarrow M$. -/
class HasTubularExpMapData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_NX : ℕ → Type*} {VF_NX : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_NX : DifferentialFormSpace Ω_NX VF_NX]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (nb : NormalBundleDFS Ω_X VF_X Ω_NX VF_NX)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (dimM dimX : ℕ)
    (hSubmfd : IsSubmanifoldInclusion i dimM dimX) where
  Ω_U₀ : ℕ → Type*
  VF_U₀ : Type*
  inst_U₀ : DifferentialFormSpace Ω_U₀ VF_U₀
  exp_map : @DFSMorphism Ω_U₀ VF_U₀ Ω_M VF_M inst_U₀ inst_M
  j₀ : @DFSMorphism Ω_U₀ VF_U₀ Ω_NX VF_NX inst_U₀ inst_NX
  s₀ : @DFSMorphism Ω_X VF_X Ω_U₀ VF_U₀ inst_X inst_U₀
  hU₀_nbhd : @IsOpenNeighborhoodOf Ω_X VF_X Ω_U₀ VF_U₀ Ω_NX VF_NX
    inst_X inst_U₀ inst_NX nb.zeroSection j₀ s₀
  hd_exp_id : ∀ {p : ℕ} (α : Ω_M p), s₀.pullback (exp_map.pullback α) = i.pullback α

/-- The output of the *inverse function theorem* applied to the exponential map: a
DFS-diffeomorphism $\varphi : U_0 \xrightarrow{\sim} U_1$ where $U_1 \subseteq M$, together
with the factorization $\exp = \mathrm{incl}_{U_1 \hookrightarrow M} \circ \varphi$. -/
class HasIFTData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_NX : ℕ → Type*} {VF_NX : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_U₀ : ℕ → Type*} {VF_U₀ : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_NX : DifferentialFormSpace Ω_NX VF_NX]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_U₀ : DifferentialFormSpace Ω_U₀ VF_U₀]
    (nb : NormalBundleDFS Ω_X VF_X Ω_NX VF_NX)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (exp_map : DFSMorphism Ω_U₀ VF_U₀ Ω_M VF_M)
    (j₀ : DFSMorphism Ω_U₀ VF_U₀ Ω_NX VF_NX)
    (s₀ : DFSMorphism Ω_X VF_X Ω_U₀ VF_U₀)
    (hU₀_nbhd : IsOpenNeighborhoodOf nb.zeroSection j₀ s₀)
    (hd_exp_id : ∀ {p : ℕ} (α : Ω_M p), s₀.pullback (exp_map.pullback α) = i.pullback α) where
  Ω_U₁ : ℕ → Type*
  VF_U₁ : Type*
  inst_U₁ : DifferentialFormSpace Ω_U₁ VF_U₁
  φ : @DFSMorphism Ω_U₀ VF_U₀ Ω_U₁ VF_U₁ inst_U₀ inst_U₁
  φ_inv : @DFSMorphism Ω_U₁ VF_U₁ Ω_U₀ VF_U₀ inst_U₁ inst_U₀
  incl_U₁_M : @DFSMorphism Ω_U₁ VF_U₁ Ω_M VF_M inst_U₁ inst_M
  hDiffeo : @IsDFSDiffeomorphism Ω_U₀ VF_U₀ Ω_U₁ VF_U₁ inst_U₀ inst_U₁ φ φ_inv
  exp_factors : ∀ {p : ℕ} (α : Ω_M p),
    φ.pullback (incl_U₁_M.pullback α) = exp_map.pullback α


