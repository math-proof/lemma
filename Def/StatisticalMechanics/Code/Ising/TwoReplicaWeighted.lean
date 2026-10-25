/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplicaWeighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def reflectEquiv (m : Current V) (P : Finset (Sym2 V)) :
    {K : Current V // ∀ e, K e ≤ m e} ≃ {K : Current V // ∀ e, K e ≤ m e} where
  toFun K := ⟨reflect m P K.1, reflect_le m P K.2⟩
  invFun K := ⟨reflect m P K.1, reflect_le m P K.2⟩
  left_inv K := Subtype.ext (reflect_involutive m P K.2)
  right_inv K := Subtype.ext (reflect_involutive m P K.2)


noncomputable def splitWeightedSum (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (F : ℝ)
    (A : Finset V) : ℝ :=
  ∑ K : {K : Current V // ∀ e, K e ≤ m e},
    (if Sharpness.sources G K.1 = A
      then F * (Sharpness.weight G β J K.1 * Sharpness.weight G β J (fun e => m e - K.1 e))
      else 0)


end Ising
end StatMech
