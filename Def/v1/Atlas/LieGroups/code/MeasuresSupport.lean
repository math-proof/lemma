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
