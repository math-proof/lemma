/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


def piRestrict (K : Set E) (x : ∀ e, S e) : ∀ i : {e : E // e ∈ K}, S i :=
  fun i => x i


noncomputable def piExtendOn (K : Set E) (base : ∀ e, S e)
    (y : ∀ i : {e : E // e ∈ K}, S i) : ∀ e, S e := by
  classical
  intro e
  by_cases he : e ∈ K
  · exact y ⟨e, he⟩
  · exact base e

end StatMech.FrontierA
