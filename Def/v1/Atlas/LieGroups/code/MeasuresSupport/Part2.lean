/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MeasuresSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.Algebra.Module.WeakDual
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import Def.v1.Atlas.LieGroups.code.CompactMeasures
public import Theorem.Complex.Eq_Sum_Mul
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.Algebra.UniformConvergence
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Instance.v1.Atlas.LieGroups.code.MeasuresSupport

@[expose] public section

noncomputable section

open Filter Topology

namespace ConcreteMeasSupp

open Filter Topology

variable {X : Type*} [TopologicalSpace X]

def IsSupportedIn (μ : C(X, ℂ) →L[ℂ] ℂ) (K : Set X) : Prop :=
  ∀ f : C(X, ℂ), (∀ x ∈ K, f x = 0) → μ f = 0

def IsWeakStarCauchy (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)) : Prop :=
  ∀ f : C(X, ℂ), CauchySeq (fun n => μ n f)

def TendstoWeakStar (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)) (μ₀ : C(X, ℂ) →L[ℂ] ℂ) : Prop :=
  ∀ f : C(X, ℂ), Tendsto (fun n => μ n f) atTop (nhds (μ₀ f))

def functionalSupport (μ : C(X, ℂ) →L[ℂ] ℂ) : Set X :=
  {x : X | ∀ U ∈ nhds x, ∃ g : C(X, ℂ), (∀ y, y ∉ U → g y = 0) ∧ μ g ≠ 0}

noncomputable def toComplexCM : C(ℝ, ℂ) := ⟨Complex.ofReal, Complex.continuous_ofReal⟩

end ConcreteMeasSupp
end
