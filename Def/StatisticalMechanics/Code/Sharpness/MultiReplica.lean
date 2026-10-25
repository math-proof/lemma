/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean -/

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
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def tripleEquivSigma {E : Type*} :
    ((E → ℕ) × (E → ℕ) × (E → ℕ)) ≃
      Σ m : (E → ℕ), {pq : (E → ℕ) × (E → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} where
  toFun klm :=
    ⟨fun e => klm.1 e + klm.2.1 e + klm.2.2 e,
      ⟨(klm.1, klm.2.1), fun e => by simp only; omega⟩⟩
  invFun s := (s.2.1.1, s.2.1.2, fun e => s.1 e - s.2.1.1 e - s.2.1.2 e)
  left_inv := by
    rintro ⟨k, l, m⟩
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext e; simp only []; omega
  right_inv := by
    rintro ⟨m, ⟨⟨p, q⟩, hpq⟩⟩
    have h1 : (fun e => p e + q e + (m e - p e - q e)) = m := by
      ext e; have h := hpq e; simp only at h; omega
    exact Sigma.subtype_ext h1 (by simp only)


end Sharpness
end StatMech
