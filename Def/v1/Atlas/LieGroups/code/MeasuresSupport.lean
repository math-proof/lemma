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
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.Algebra.UniformConvergence
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

@[expose] public section

noncomputable section

open Filter Topology

namespace Meas

def embedMap (X : Type*) [TopologicalSpace X]
    (MX : Type*) [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] : (X →₀ ℂ) →ₗ[ℂ] MX :=
  Finsupp.linearCombination ℂ (CompactlySupportedMeasureSpace.dirac (X := X) (MX := MX))

def atomicIn {X : Type*} [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] (K : Set X) : Set MX :=
  (embedMap X MX) '' { f : X →₀ ℂ | ↑f.support ⊆ K }

def IsSupportedIn {X : Type*} [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] (μ : MX) (K : Set X) : Prop :=
  μ ∈ closure (atomicIn K)

end Meas


namespace Meas

def functionalSupp (X : Type*) [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] (μ : MX) : Set X :=
  ⋂₀ { K : Set X | IsClosed K ∧ IsSupportedIn (X := X) μ K }

end Meas
end
