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
import Def.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part4
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- An algebraic *deformation retract* of $U$ onto $X$: a relative homotopy operator
together with an injectivity condition at degree 0 (forms of degree 0 with vanishing
differential and vanishing pullback are zero). -/
structure HasDeformationRetract
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_U : ℕ → Type*} {VF_U : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_U : DifferentialFormSpace Ω_U VF_U]
    (i : DFSMorphism Ω_X VF_X Ω_U VF_U) where
  π : DFSMorphism Ω_U VF_U Ω_X VF_X
  retraction : ∀ {p : ℕ} (α : Ω_X p), i.pullback (π.pullback α) = α
  K : ∀ {p : ℕ}, Ω_U (p + 1) → Ω_U p
  K_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω_U (p + 1)), K (r • α) = r • K α
  homotopy_formula : ∀ {p : ℕ} (β : Ω_U (p + 1)),
    inst_U.d (K β) + K (inst_U.d β) = β - π.pullback (i.pullback β)
  K_vanishes_on_X : ∀ {p : ℕ} (β : Ω_U (p + 1)), i.pullback (K β) = 0
  deg0_injectivity : ∀ (β : Ω_U 0), inst_U.d β = (0 : Ω_U 1) →
    i.pullback β = (0 : Ω_X 0) → β = (0 : Ω_U 0)

/-- Abstract data for the *normal bundle* $NX \to X$ at the level of differential forms:
a zero-section morphism $X \to NX$ and a projection $NX \to X$ whose composition
pulled back to forms is the identity on $\Omega^*(X)$. -/
structure NormalBundleDFS
    (Ω_X : ℕ → Type*) (VF_X : Type*)
    (Ω_NX : ℕ → Type*) (VF_NX : Type*)
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_NX : DifferentialFormSpace Ω_NX VF_NX] where
  zeroSection : DFSMorphism Ω_X VF_X Ω_NX VF_NX
  projection : DFSMorphism Ω_NX VF_NX Ω_X VF_X
  proj_section : ∀ {p : ℕ} (α : Ω_X p),
    zeroSection.pullback (projection.pullback α) = α


/-- Predicate that the DFS morphism $i : X \hookrightarrow M$ comes from a smooth
submanifold inclusion of dimensions $\dim X \le \dim M$. -/
structure IsSubmanifoldInclusion
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [DifferentialFormSpace Ω_X VF_X]
    [DifferentialFormSpace Ω_M VF_M]
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (dimM dimX : ℕ) : Prop where
  dim_le : dimX ≤ dimM


/-- Compatibility predicate stating that $U \subseteq N$ is an open neighborhood of
$X \subseteq N$: the inclusion $X \hookrightarrow N$ factors as
$X \hookrightarrow U \hookrightarrow N$ on differential forms. -/
structure IsOpenNeighborhoodOf
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_U : ℕ → Type*} {VF_U : Type*}
    {Ω_N : ℕ → Type*} {VF_N : Type*}
    [DifferentialFormSpace Ω_X VF_X]
    [inst_U : DifferentialFormSpace Ω_U VF_U]
    [DifferentialFormSpace Ω_N VF_N]
    (incl_X_N : DFSMorphism Ω_X VF_X Ω_N VF_N)
    (incl_U_N : @DFSMorphism Ω_U VF_U Ω_N VF_N inst_U _)
    (incl_X_U : @DFSMorphism Ω_X VF_X Ω_U VF_U _ inst_U) : Prop where
  compatible : ∀ {p : ℕ} (α : Ω_N p),
    incl_X_U.pullback (incl_U_N.pullback α) = incl_X_N.pullback α

/-- A pair of DFS morphisms $\varphi, \varphi^{-1}$ form a *DFS diffeomorphism* if their
pullbacks are mutually inverse on all differential forms. -/
structure IsDFSDiffeomorphism
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (φ : @DFSMorphism Ω₁ VF₁ Ω₂ VF₂ inst₁ inst₂)
    (φ_inv : @DFSMorphism Ω₂ VF₂ Ω₁ VF₁ inst₂ inst₁) : Prop where
  left_inv : ∀ {p : ℕ} (α : Ω₂ p), φ_inv.pullback (φ.pullback α) = α
  right_inv : ∀ {p : ℕ} (α : Ω₁ p), φ.pullback (φ_inv.pullback α) = α


