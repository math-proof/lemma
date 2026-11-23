/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplectomorphismFixedPoints.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Structure.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part7
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.WeinsteinNeighborhood
public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplectomorphismFixedPoints

@[expose] public section

set_option autoImplicit false


noncomputable section

open Filter Topology


/-- $\varphi : M \to M$ is a symplectomorphism if $\varphi^* \omega = \omega$, i.e. $\omega_{\varphi(x)}(d\varphi_x v, d\varphi_x w) = \omega_x(v, w)$. -/
def IsSymplectomorphism
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (ω : SymplecticForm I M)
    (φ : M → M) : Prop :=
  ∀ (x : M) (v w : E),
    ω.form (φ x) (mfderiv I I φ x v) (mfderiv I I φ x w) = ω.form x v w

/-- $x$ is a critical point of $f : M \to \mathbb{R}$ if $df_x = 0$. -/
def IsCriticalPt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M → ℝ) (x : M) : Prop :=
  mfderiv I (modelWithCornersSelf ℝ ℝ) f x = 0

/-- A $1$-form $\mu : M \to E^*$ is closed if its derivative is symmetric: $D\mu_x(v)(w) = D\mu_x(w)(v)$. -/
def IsClosed1Form
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (μ : M → (E →L[ℝ] ℝ)) : Prop :=
  ∀ (x : M) (v w : E),
    (show E →L[ℝ] ℝ from mfderiv I (modelWithCornersSelf ℝ (E →L[ℝ] ℝ)) μ x v) w =
    (show E →L[ℝ] ℝ from mfderiv I (modelWithCornersSelf ℝ (E →L[ℝ] ℝ)) μ x w) v

/-- $H^1(M, \mathbb{R}) = 0$: every smooth closed $1$-form on $M$ is exact, i.e. $\mu = dh$ for some smooth $h$. -/
def DeRhamH1Vanishes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop :=
  ∀ (μ : M → (E →L[ℝ] ℝ)),
    ContMDiff I (modelWithCornersSelf ℝ (E →L[ℝ] ℝ)) ⊤ μ →
    IsClosed1Form I μ →
    ∃ (h : M → ℝ), ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ h ∧
      ∀ x : M, mfderiv I (modelWithCornersSelf ℝ ℝ) h x = μ x

/-- $\varphi$ is $C^1$-close to the identity: smooth, with $\|d\varphi_x - \mathrm{id}\| < 1$ at every point. -/
def IsC1CloseToId
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (φ : M → M) : Prop :=
  ContMDiff I I ⊤ φ ∧
    ∀ (x : M), ‖(show E →L[ℝ] E from mfderiv I I φ x) -
      ContinuousLinearMap.id ℝ E‖ < 1

end
