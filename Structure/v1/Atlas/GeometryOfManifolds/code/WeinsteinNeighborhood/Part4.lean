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
import Class.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- Packaging of the *conclusion* of the tubular neighborhood theorem: open
neighborhoods $U_0$ of $X$ in $NX$ and $U_1$ of $X$ in $M$, a DFS-diffeomorphism
$\varphi : U_0 \xrightarrow{\sim} U_1$ that restricts to the identity on $X$, together with
the relevant inclusions and the open-neighborhood data on both sides. -/
structure TubularNeighborhoodData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_NX : ℕ → Type*} {VF_NX : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_NX : DifferentialFormSpace Ω_NX VF_NX]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (nb : NormalBundleDFS Ω_X VF_X Ω_NX VF_NX)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M) where
  Ω_U₀ : ℕ → Type*
  VF_U₀ : Type*
  inst_U₀ : DifferentialFormSpace Ω_U₀ VF_U₀
  Ω_U₁ : ℕ → Type*
  VF_U₁ : Type*
  inst_U₁ : DifferentialFormSpace Ω_U₁ VF_U₁
  φ : @DFSMorphism Ω_U₀ VF_U₀ Ω_U₁ VF_U₁ inst_U₀ inst_U₁
  φ_inv : @DFSMorphism Ω_U₁ VF_U₁ Ω_U₀ VF_U₀ inst_U₁ inst_U₀
  j₀ : @DFSMorphism Ω_U₀ VF_U₀ Ω_NX VF_NX inst_U₀ inst_NX
  s₀ : @DFSMorphism Ω_X VF_X Ω_U₀ VF_U₀ inst_X inst_U₀
  j₁ : @DFSMorphism Ω_X VF_X Ω_U₁ VF_U₁ inst_X inst_U₁
  incl_U₁_M : @DFSMorphism Ω_U₁ VF_U₁ Ω_M VF_M inst_U₁ inst_M
  hDiffeo : @IsDFSDiffeomorphism Ω_U₀ VF_U₀ Ω_U₁ VF_U₁ inst_U₀ inst_U₁ φ φ_inv
  hU₀_nbhd : @IsOpenNeighborhoodOf Ω_X VF_X Ω_U₀ VF_U₀ Ω_NX VF_NX
    inst_X inst_U₀ inst_NX nb.zeroSection j₀ s₀
  hU₁_nbhd : @IsOpenNeighborhoodOf Ω_X VF_X Ω_U₁ VF_U₁ Ω_M VF_M
    inst_X inst_U₁ inst_M i incl_U₁_M j₁
  hφ_X : ∀ {p : ℕ} (α : Ω_U₁ p), s₀.pullback (φ.pullback α) = j₁.pullback α

