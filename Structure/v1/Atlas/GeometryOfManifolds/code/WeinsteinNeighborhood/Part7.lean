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
import Class.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part3
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- The Mathlib analog of `C1CloseLagrangian`: data of a smooth function
$h : X \to \mathbb{R}$ whose critical points correspond exactly to intersection points
of $X$ with a $C^1$-close submanifold $Y$. -/
structure C1CloseSubmanifold_mfld
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HH : Type*} [TopologicalSpace HH]
    (I : ModelWithCorners ℝ E HH)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HH M] [IsManifold I ⊤ M]
    (X : Type*) [TopologicalSpace X] [ChartedSpace HH X] [IsManifold I ⊤ X]
    (i : X → M) where
  isIntersectionPt : X → Prop
  h : X → ℝ
  h_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ h
  crit_iff_intersection : ∀ x : X,
    isIntersectionPt x ↔ mfderiv I (modelWithCornersSelf ℝ ℝ) h x = 0

/-- A slimmer variant of `C1CloseSubmanifold_mfld` carrying only the smooth function $h$
on $X$ and the intersection-vs-critical-point equivalence. -/
structure C1CloseLagrangianMfld
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HH : Type*} [TopologicalSpace HH]
    (I : ModelWithCorners ℝ E HH)
    (X : Type*) [TopologicalSpace X] [ChartedSpace HH X] [IsManifold I ⊤ X] where
  h : X → ℝ
  h_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ h
  isIntersectionPt : X → Prop
  crit_iff_intersection : ∀ x : X,
    isIntersectionPt x ↔ mfderiv I (modelWithCornersSelf ℝ ℝ) h x = 0

/-- **Extreme value theorem giving $\ge 2$ critical points.** On a compact nontrivial
manifold $X$, every smooth $h : X \to \mathbb{R}$ has at least two distinct critical points. -/
structure HasH1Vanishing_Mathlib
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  exact_of_closed : ∀ (ω : E → E [⋀^Fin 1]→L[ℝ] ℝ),
    (∀ x : E, extDeriv ω x = 0) →
    ∃ (f : E → E [⋀^Fin 0]→L[ℝ] ℝ), ∀ x : E, extDeriv f x = ω x

open scoped Manifold in
/-- Mathlib-style packaging of the Weinstein tubular neighborhood: open sets
$U \subseteq M$ containing $X$ and $U_0 \subseteq E \times E$ containing the zero
section, with a diffeomorphism $\Phi : U_0 \xrightarrow{\sim} U$ taking the zero section
into $X$ and (placeholder) preserving the symplectic structure. -/
structure WeinsteinTubular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
    (ω : M → E [⋀^Fin 2]→L[ℝ] ℝ)
    (i : X → M)
    (hi : ContMDiff I I ⊤ i) where
  U : TopologicalSpace.Opens M
  hU_contains_X : ∀ x : X, i x ∈ U
  U₀ : TopologicalSpace.Opens (E × E)
  hU₀_zero_section : ∀ v : E, (v, (0 : E)) ∈ U₀
  Φ : Diffeomorph (modelWithCornersSelf ℝ (E × E)) I U₀ U ⊤
  hΦ_identity_on_X : ∀ (v : E) (hv : (v, (0 : E)) ∈ U₀),
    (Φ ⟨(v, 0), hv⟩ : M) ∈ Set.range i
  hΦ_symplectic : True


open scoped Manifold in
/-- Mathlib-style packaging of the (non-symplectic) tubular neighborhood theorem:
neighborhoods $U_1 \ni X$ in $M$ and $U_0 \ni$ zero section in $E \times E$, and a
diffeomorphism $\varphi : U_0 \to U_1$ mapping the zero section into $X$. -/
structure tubular_neighborhood_theorem_book_Mathlib
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
    (i : X → M)
    (hi : ContMDiff I I ⊤ i) where
  U₁ : TopologicalSpace.Opens M
  hU₁_contains_X : ∀ x : X, i x ∈ U₁
  U₀ : TopologicalSpace.Opens (E × E)
  hU₀_zero : ∀ v : E, (v, (0 : E)) ∈ U₀
  φ : Diffeomorph (modelWithCornersSelf ℝ (E × E)) I U₀ U₁ ⊤
  hφ_preserves_X : ∀ (v : E) (hv : (v, (0 : E)) ∈ U₀),
    (φ ⟨(v, 0), hv⟩ : M) ∈ Set.range i

open scoped Manifold in
/-- **Existence of an exponential-like map** in the Mathlib setting (axiomatic). For any
smooth injective $i : X \to M$, there exists an open set $U_0 \subseteq E_X \times E_N$
containing the zero section and a smooth map $\exp : U_0 \to M$ such that the zero
section lands in $i(X)$, $\exp$ is locally injective, and $i(X) \subseteq \mathrm{im}(\exp)$. -/
structure C1CloseLagrangian_Mathlib
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Type*) where
  chart : X → E
  μ : E → E [⋀^Fin 1]→L[ℝ] ℝ
  μ_closed : ∀ x : E, extDeriv μ x = 0
  isZeroAt : X → Prop
  zero_iff : ∀ x : X, isZeroAt x ↔ μ (chart x) = 0

