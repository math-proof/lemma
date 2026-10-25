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

end
