/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

noncomputable section

open scoped TensorProduct
open Filter Topology Classical

class CompactlySupportedMeasureSpace
    (X : Type*) [TopologicalSpace X]
    (MX : Type*) [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX] where
  dirac : X → MX
  evalPairing : MX →ₗ[ℂ] C(X, ℂ) →ₗ[ℂ] ℂ
  evalPairing_dirac : ∀ (x : X) (f : C(X, ℂ)), evalPairing (dirac x) f = f x
  evalPairing_continuous : ∀ (f : C(X, ℂ)), Continuous (fun μ : MX => evalPairing μ f)
  hasCompactSupport : ∀ (μ : MX), ∃ (K : Set X), IsCompact K ∧
    ∀ (f : C(X, ℂ)), (∀ x ∈ K, f x = 0) → evalPairing μ f = 0
  topology_eq_initial : ∀ (μ : MX), 𝓝 μ = ⨅ (f : C(X, ℂ)),
    Filter.comap (fun ν => evalPairing ν f) (𝓝 (evalPairing μ f))

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

section BLTExtension

variable {D₁ : Type*} [AddCommGroup D₁] [Module ℂ D₁]
variable {D₂ : Type*} [AddCommGroup D₂] [Module ℂ D₂]
variable {M₁ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [TopologicalSpace M₁]
variable {M₂ : Type*} [AddCommGroup M₂] [Module ℂ M₂] [TopologicalSpace M₂]
variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]

end BLTExtension

end
