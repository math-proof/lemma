/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def pairEquivSigma {E : Type*} :
    ((E → ℕ) × (E → ℕ)) ≃ Σ m : (E → ℕ), {p : E → ℕ // p ≤ m} where
  toFun pq := ⟨fun e => pq.1 e + pq.2 e, ⟨pq.1, fun e => Nat.le_add_right _ _⟩⟩
  invFun mp := (mp.2.1, fun e => mp.1 e - mp.2.1 e)
  left_inv := by rintro ⟨p, q⟩; ext e <;> simp
  right_inv := by
    rintro ⟨m, ⟨p, hp⟩⟩
    have hm : (fun e => p e + (m e - p e)) = m := by
      ext e; exact Nat.add_sub_cancel' (hp e)
    simp only
    exact Sigma.subtype_ext hm rfl


end Sharpness
end StatMech
