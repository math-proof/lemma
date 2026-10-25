/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MeasuresSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Def.v1.Atlas.LieGroups.code.CompactMeasures
import Lemma.Complex.Eq_Sum_Mul
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Algebra.UniformConvergence
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Instance.v1.Atlas.LieGroups.code.MeasuresSupport


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
