/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox.Part4
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


universe w


theorem finiteQuotientRepresentative_rightInverse
    [∀ e, Nonempty (S e)] {n : E → ℕ} (q : ∀ e, S e → Fin (n e))
    (e : E) (x : S e) :
    q e (finiteQuotientRepresentative q e (q e x)) = q e x := by
  classical
  let hex : ∃ y, q e y = q e x := ⟨x, rfl⟩
  rw [finiteQuotientRepresentative, dif_pos hex]
  exact Classical.choose_spec hex

end StatMech.FrontierA
