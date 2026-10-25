/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Lemma.Complex.IsKFinite0
import Def.v1.Atlas.LieGroups.code.SmoothVectors
import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Def.v1.Atlas.LieGroups.code.GKModuleDefs.Part2
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Lie.Semisimple.Defs
universe uLie


noncomputable section

open scoped Manifold

opaque principalSymbolOn (N : ℕ)
    (D : (EuclideanSpace ℝ (Fin N) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin N) → ℝ)) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) → ℝ

def IsEllipticOnOpen (N : ℕ)
    (D : (EuclideanSpace ℝ (Fin N) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin N) → ℝ))
    (U : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∀ (x : EuclideanSpace ℝ (Fin N)), x ∈ U →
    ∀ (p : EuclideanSpace ℝ (Fin N)), p ≠ 0 → principalSymbolOn N D x p ≠ 0

opaque HasAnalyticCoefficientsOn (N : ℕ)
    (D : (EuclideanSpace ℝ (Fin N) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin N) → ℝ))
    (U : Set (EuclideanSpace ℝ (Fin N))) : Prop

def IsEllipticAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (D : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (x : X) : Prop :=
  ∀ (p : E), p ≠ 0 → principalSymbolManifold I D x p ≠ 0

def IsEllipticOnManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (D : (X → ℝ) →ₗ[ℝ] (X → ℝ)) : Prop :=
  ∀ (x : X), IsEllipticAt I D x

opaque HasLocallyAnalyticCoeffs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (D : (X → ℝ) →ₗ[ℝ] (X → ℝ)) : Prop

def IsEllipticWithAnalyticCoeffs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (D : (X → ℝ) →ₗ[ℝ] (X → ℝ)) : Prop :=

  IsEllipticOnManifold I D ∧

  HasLocallyAnalyticCoeffs I D

namespace ContinuousRep

section WeaklyAnalytic

universe uFsec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H]

variable (I : ModelWithCorners ℝ E H)

variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]

variable [LieGroup I ⊤ G]

variable {F : Type uFsec} [NormedAddCommGroup F] [NormedSpace ℂ F]

def IsWeaklyAnalyticVector (π : ContinuousRep G F) (v : F) : Prop :=
  ∀ h : F →L[ℂ] ℂ, ∀ g₀ : G,
    ∃ (s : Set E), s ∈ nhds (I (chartAt H g₀ g₀)) ∧
    AnalyticOnNhd ℝ
      (fun e : E => (h ((π.toMonoidHom ((chartAt H g₀).symm (I.symm e))) v)).re)
      s

def weaklyAnalyticSet (π : ContinuousRep G F) : Set F :=
  { v | π.IsWeaklyAnalyticVector I v }

end WeaklyAnalytic
end ContinuousRep
end
