/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Derivation.Lie
import Structure.v1.Atlas.LieGroups.code.DModules.Part2
universe u v w


namespace DModules

open scoped TensorProduct

section Connections

noncomputable def covariantDerivative {k : Type u} [CommRing k] {A : Type v} [CommRing A]
    [Algebra k A] {M : Type w} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M]
    (v : Derivation k A A) (conn : Connection k A M) : M →ₗ[k] M :=
  ((TensorProduct.rid A M).toLinearMap ∘ₗ
    (LinearMap.lTensor M v.liftKaehlerDifferential)).restrictScalars k ∘ₗ conn.nabla

noncomputable def curvature {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
    {M : Type w} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    (conn : Connection k A M) (v w : Derivation k A A) : M →ₗ[k] M :=
  (covariantDerivative v conn) ∘ₗ (covariantDerivative w conn) -
  (covariantDerivative w conn) ∘ₗ (covariantDerivative v conn) -
  covariantDerivative ⁅v, w⁆ conn

def Connection.IsFlat {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
    {M : Type w} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    (conn : Connection k A M) : Prop :=
  ∀ v w : Derivation k A A, curvature conn v w = 0

end Connections
end DModules
