/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/BundleDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.Complex.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.BundleDFS.Part3


noncomputable section

open scoped Manifold

open Bundle


/-- Data for the normal bundle of an embedding $\iota : N \hookrightarrow M$: fibers $\mathcal{N}_x$, module structure, and the normal rank. -/
structure NormalBundleData
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN]
    (IN : ModelWithCorners ℝ EN HN)
    (N : Type*) [TopologicalSpace N] [ChartedSpace HN N]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    (IM : ModelWithCorners ℝ EM HM)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] where
  ι : N → M
  NormalFiber : N → Type*
  instACG : ∀ x, AddCommGroup (NormalFiber x)
  instMod : ∀ x, Module ℝ (NormalFiber x)
  normalRank : ℕ

namespace NormalBundleData

attribute [instance] NormalBundleData.instACG NormalBundleData.instMod

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

end NormalBundleData


/-- A $\operatorname{Spin}^{\mathbb{C}}$ structure on $M$: complex spinor bundles $W^+, W^-$ with Clifford multiplication maps $\gamma_{\pm} : TM \otimes W^{\pm} \to W^{\mp}$ and first Chern class $c_1$ of the determinant line bundle. -/
structure SpinCStructureDFS
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    (I : ModelWithCorners ℝ EM HM)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HM M]
    [IsManifold I ⊤ M] where
  SpinorPlusFiber : M → Type*
  SpinorMinusFiber : M → Type*
  instACG_plus : ∀ x, AddCommGroup (SpinorPlusFiber x)
  instMod_plus : ∀ x, Module ℂ (SpinorPlusFiber x)
  instACG_minus : ∀ x, AddCommGroup (SpinorMinusFiber x)
  instMod_minus : ∀ x, Module ℂ (SpinorMinusFiber x)
  γ_plus_to_minus : ∀ x, TangentSpace I x → (SpinorPlusFiber x →ₗ[ℂ] SpinorMinusFiber x)
  γ_minus_to_plus : ∀ x, TangentSpace I x → (SpinorMinusFiber x →ₗ[ℂ] SpinorPlusFiber x)
  c₁ : ℤ

end
