/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox.Part4
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


universe w


structure FiniteCoordinateFactorOn (K : Set E) (h : (∀ e, S e) → ℝ) where
  T : E → Type w
  fintype_T : ∀ e, Fintype (T e)
  measurableSpace_T : ∀ e, MeasurableSpace (T e)
  measurableSingleton_T : ∀ e, MeasurableSingletonClass (T e)
  q : ∀ e, S e → T e
  measurable_q : ∀ e, Measurable (q e)
  H : (∀ e, T e) → ℝ
  nonneg_H : ∀ y, 0 ≤ H y
  dependsOn_H : ∀ ⦃x y⦄, piAgreeOn K x y → H x = H y
  eq_comp : h = fun x => H (fun e => q e (x e))

structure FiniteCoordinateSetData (A : Set (∀ e, S e)) where
  n : E → ℕ
  q : ∀ e, S e → Fin (n e)
  B : Set (∀ e, Fin (n e))
  measurable_q : ∀ e, Measurable (q e)
  eq_preimage : A = (fun x e => q e (x e)) ⁻¹' B

end StatMech.FrontierA
