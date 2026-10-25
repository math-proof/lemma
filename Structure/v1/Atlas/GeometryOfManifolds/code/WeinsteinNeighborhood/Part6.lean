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
import Class.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part2
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- Existence of `HasLagrangianTubularData`: combine the geometric tubular neighborhood
data with the first-order agreement of $\omega_0$ and $\omega_1$ on $X$, then apply
the local Moser theorem to produce the required diffeomorphism $\varphi$. -/
structure DFSPointEvalX
    (Ω_X : ℕ → Type*) (VF_X : Type*) (X : Type*)
    [inst_X : DifferentialFormSpace Ω_X VF_X] where
  isZeroAt : Ω_X 1 → X → Prop

/-- Axiomatic vanishing of $H^1(X, \mathbb{R})$: every closed 1-form on $X$ is exact,
i.e. $\mu = dh$ for some smooth $h : X \to \mathbb{R}$. -/
structure HasH1Vanishing
    (Ω_X : ℕ → Type*) (VF_X : Type*)
    [inst_X : DifferentialFormSpace Ω_X VF_X] : Prop where
  exact_of_closed : ∀ (μ : Ω_X 1), inst_X.d μ = 0 → ∃ (h : Ω_X 0), μ = inst_X.d h

/-- On a compact (Hausdorff) manifold $X$, every smooth function $h : X \to \mathbb{R}$
has at least two critical points (achieving its max and min). -/
structure C1CloseLagrangian
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_TX : ℕ → Type*} {VF_TX : Type*}
    {X : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_TX : DifferentialFormSpace Ω_TX VF_TX]
    [hCot : CotangentBundleDFS Ω_X VF_X Ω_TX VF_TX]
    (ptEval : DFSPointEvalX Ω_X VF_X X)
    (S_M : SymplecticManifold Ω_M VF_M)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (hLag : IsLagrangianSubmanifold S_M i (2 * hCot.dimX) hCot.dimX) where
  μ : Ω_X 1
  μ_closed : inst_X.d μ = 0
  weinstein_intersection_iff_zero :
    ∀ (x : X), (x ∈ {p : X | ptEval.isZeroAt μ p}) ↔ ptEval.isZeroAt μ x

