/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Class.v1.Atlas.LieGroups.code.CompactMeasures

@[expose] public section

noncomputable section

open scoped TensorProduct

open Filter Topology Classical

def CompactlySupportedMeasureSpace.embed (X : Type*) [TopologicalSpace X]
    (MX : Type*) [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] :
    (X →₀ ℂ) →ₗ[ℂ] MX :=
  Finsupp.linearCombination ℂ (CompactlySupportedMeasureSpace.dirac (X := X) (MX := MX))

def concreteDirac (X : Type*) [TopologicalSpace X] (x : X) : WeakDual ℂ C(X, ℂ) :=
  ContinuousMap.evalCLM ℂ x

def concreteDiracEmbed (X : Type*) [TopologicalSpace X] :
    (X →₀ ℂ) →ₗ[ℂ] WeakDual ℂ C(X, ℂ) :=
  Finsupp.linearCombination ℂ (concreteDirac X)

def boxtimesAtomic (X Y : Type*) :
    (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ) →ₗ[ℂ] (X × Y →₀ ℂ) :=
  (TensorProduct.mk ℂ (X →₀ ℂ) (Y →₀ ℂ)).compr₂
    (finsuppTensorFinsupp' ℂ X Y).toLinearMap

def boxtimesAtomicToMeas (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ) →ₗ[ℂ] WeakDual ℂ C(X × Y, ℂ) :=
  (boxtimesAtomic X Y).compr₂ (concreteDiracEmbed (X × Y))

end
