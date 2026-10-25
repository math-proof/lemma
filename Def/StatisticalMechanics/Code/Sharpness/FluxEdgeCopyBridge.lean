/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
open Finset BigOperators
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace FluxEdgeCopy

variable {E : Type*} [Fintype E] [DecidableEq E] {β : E → Type*}
  [∀ e, Fintype (β e)] [∀ e, DecidableEq (β e)]


noncomputable def sigmaFinsetEquivPi : Finset (Σ e : E, β e) ≃ Π e : E, Finset (β e) where
  toFun S := fun e => (univ : Finset (β e)).filter (fun b => (⟨e, b⟩ : Σ e, β e) ∈ S)
  invFun f := univ.filter (fun i : Σ e, β e => i.2 ∈ f i.1)
  left_inv := by intro S; ext i; obtain ⟨e, b⟩ := i; simp
  right_inv := by intro f; ext e b; simp

end FluxEdgeCopy
end Sharpness
end StatMech
