/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/POUSeqDensityHelpers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.WeakDual
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.PartitionOfUnity
public import Instance.v1.Atlas.LieGroups.code.POUSeqDensityHelpers

@[expose] public section

set_option linter.unusedSectionVars false

open TopologicalSpace Metric Set Filter Topology


noncomputable section

section POUAndDirac

variable {X : Type*} [MetricSpace X] [CompactSpace X]

def ContinuousMap.liftReal (f : C(X, ℝ)) : C(X, ℂ) :=
  (⟨Complex.ofReal, Complex.continuous_ofReal⟩ : C(ℝ, ℂ)).comp f

def diracCLM (x : X) : WeakDual ℂ C(X, ℂ) :=
  (ContinuousMap.evalCLM ℂ x : C(X, ℂ) →L[ℂ] ℂ)

def diracPOUApprox
    (μ : WeakDual ℂ C(X, ℂ))
    (S : Finset X)
    (φ : S → C(X, ℝ))
    : WeakDual ℂ C(X, ℂ) :=
  ∑ s : S, (μ (ContinuousMap.liftReal (φ s))) • diracCLM (s : X)

end POUAndDirac
end
