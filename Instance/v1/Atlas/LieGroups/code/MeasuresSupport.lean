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
public import Def.v1.Atlas.LieGroups.code.MeasuresSupport

@[expose] public section

noncomputable section

open Filter Topology

noncomputable instance ContinuousMap.instIsUniformAddGroupComplex
    {X : Type*} [TopologicalSpace X] :
    IsUniformAddGroup C(X, ℂ) :=
  IsUniformInducing.isUniformAddGroup
    ({ toFun := ContinuousMap.toUniformOnFunIsCompact
       map_zero' := rfl
       map_add' := fun _ _ => rfl } : C(X, ℂ) →+ UniformOnFun X ℂ {K | IsCompact K})
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing

end
