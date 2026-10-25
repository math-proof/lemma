/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox.Part2
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


theorem measurable_piExtendOn (K : Set E) (base : ∀ e, S e) :
    Measurable (piExtendOn K base) := by
  classical
  apply measurable_pi_lambda
  intro e
  by_cases he : e ∈ K
  · simpa [piExtendOn, he] using
      (@measurable_pi_apply {e : E // e ∈ K} (fun i => S i.1) _ ⟨e, he⟩)
  · simpa [piExtendOn, he] using
      (measurable_const : Measurable
        (fun _ : (∀ i : {e : E // e ∈ K}, S i) => base e))

theorem piExtendOn_agreeOn (K : Set E) (base : ∀ e, S e)
    (x : ∀ e, S e) :
    piAgreeOn K x (piExtendOn K base (piRestrict K x)) := by
  intro e he
  simp [piExtendOn, piRestrict, he]

end StatMech.FrontierA
